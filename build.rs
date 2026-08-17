#[cfg(feature = "compressed-step-metadata")]
mod compressed {
    use std::{
        collections::{BTreeMap, HashMap},
        env, fs,
        io::{self, Write},
        path::{Path, PathBuf},
    };

    use proc_macro2::{TokenStream, TokenTree};
    use syn::{LitInt, LitStr, visit::Visit};

    const RECORD_BYTES: usize = 12;

    #[derive(Debug)]
    struct RuleText {
        order: u16,
        source: String,
        description: String,
    }

    struct RuleVisitor {
        rules: Vec<RuleText>,
    }

    impl<'ast> Visit<'ast> for RuleVisitor {
        fn visit_macro(&mut self, node: &'ast syn::Macro) {
            if node
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "rubi_rule")
            {
                if let Some(rule) = parse_rule_text(&node.tokens) {
                    self.rules.push(rule);
                }
            }
            syn::visit::visit_macro(self, node);
        }
    }

    fn parse_rule_text(tokens: &TokenStream) -> Option<RuleText> {
        let mut order = None;
        let mut source = None;
        let mut description = None;
        let mut tokens = tokens.clone().into_iter().peekable();

        while let Some(token) = tokens.next() {
            let TokenTree::Ident(field) = token else {
                continue;
            };
            let field = field.to_string();
            if !matches!(field.as_str(), "order" | "source" | "desc") {
                continue;
            }
            let Some(TokenTree::Punct(colon)) = tokens.next() else {
                continue;
            };
            if colon.as_char() != ':' {
                continue;
            }
            let Some(TokenTree::Literal(value)) = tokens.next() else {
                continue;
            };
            let value = value.to_string();
            match field.as_str() {
                "order" => order = syn::parse_str::<LitInt>(&value).ok()?.base10_parse().ok(),
                "source" => source = Some(syn::parse_str::<LitStr>(&value).ok()?.value()),
                "desc" => description = Some(syn::parse_str::<LitStr>(&value).ok()?.value()),
                _ => unreachable!(),
            }
        }

        Some(RuleText {
            order: order?,
            source: source?,
            description: description?,
        })
    }

    fn intern_text(
        value: &str,
        texts: &mut Vec<u8>,
        interned: &mut HashMap<String, (u32, u16)>,
    ) -> io::Result<(u32, u16)> {
        if let Some(position) = interned.get(value) {
            return Ok(*position);
        }
        let offset = u32::try_from(texts.len())
            .map_err(|_| io::Error::other("Rubi rule text catalog exceeds 4 GiB"))?;
        let len = u16::try_from(value.len())
            .map_err(|_| io::Error::other("one Rubi rule text exceeds 64 KiB"))?;
        texts.extend_from_slice(value.as_bytes());
        interned.insert(value.to_owned(), (offset, len));
        Ok((offset, len))
    }

    fn write_u32(record: &mut [u8], offset: usize, value: u32) {
        record[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    fn write_u16(record: &mut [u8], offset: usize, value: u16) {
        record[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
    }

    fn collect_rule_files(directory: &Path) -> io::Result<Vec<PathBuf>> {
        let mut files = fs::read_dir(directory)?
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
            .collect::<Vec<_>>();
        files.sort();
        Ok(files)
    }

    pub fn build() -> io::Result<()> {
        let rules_directory = Path::new("src/rules");
        println!("cargo:rerun-if-changed={}", rules_directory.display());

        let mut rules_by_order = BTreeMap::new();
        for path in collect_rule_files(rules_directory)? {
            println!("cargo:rerun-if-changed={}", path.display());
            let source = fs::read_to_string(&path)?;
            let syntax = syn::parse_file(&source).map_err(|error| {
                io::Error::other(format!("failed to parse {}: {error}", path.display()))
            })?;
            let mut visitor = RuleVisitor { rules: Vec::new() };
            visitor.visit_file(&syntax);
            for rule in visitor.rules {
                if let Some(previous) = rules_by_order
                    .insert(rule.order, (rule.source.clone(), rule.description.clone()))
                {
                    if previous != (rule.source, rule.description) {
                        return Err(io::Error::other(format!(
                            "Rubi rule order {} has conflicting explanation text",
                            rule.order
                        )));
                    }
                }
            }
        }

        let Some(max_order) = rules_by_order.keys().next_back().copied() else {
            return Err(io::Error::other("no Rubi rule explanation text found"));
        };
        let record_count = usize::from(max_order) + 1;
        let mut directory = vec![0; record_count * RECORD_BYTES];
        let mut texts = Vec::new();
        let mut interned = HashMap::new();

        for (order, (source, description)) in &rules_by_order {
            let (source_offset, source_len) = intern_text(source, &mut texts, &mut interned)?;
            let (description_offset, description_len) =
                intern_text(description, &mut texts, &mut interned)?;
            let start = usize::from(*order) * RECORD_BYTES;
            let record = &mut directory[start..start + RECORD_BYTES];
            write_u32(record, 0, source_offset);
            write_u32(record, 4, description_offset);
            write_u16(record, 8, source_len);
            write_u16(record, 10, description_len);
        }

        let mut uncompressed = directory;
        uncompressed.extend_from_slice(&texts);
        let mut compressed = Vec::new();
        {
            let mut compressor = brotli::CompressorWriter::new(&mut compressed, 4096, 11, 22);
            compressor.write_all(&uncompressed)?;
        }

        let output_directory = PathBuf::from(env::var_os("OUT_DIR").ok_or_else(|| {
            io::Error::other("Cargo did not provide OUT_DIR to the Rubi build script")
        })?);
        fs::write(output_directory.join("rubi_rule_texts.br"), compressed)?;
        fs::write(
            output_directory.join("rubi_rule_texts.rs"),
            format!(
                "const RUBI_RULE_TEXT_RECORD_BYTES: usize = {RECORD_BYTES};\n\
             const RUBI_RULE_TEXT_RECORD_COUNT: usize = {record_count};\n\
             #[cfg(test)]\n\
             const RUBI_RULE_TEXT_RULE_COUNT: usize = {};\n\
             const RUBI_RULE_TEXT_DIRECTORY_BYTES: usize = {};\n\
             static RUBI_RULE_TEXT_COMPRESSED: &[u8] = include_bytes!(concat!(env!(\"OUT_DIR\"), \"/rubi_rule_texts.br\"));\n",
                rules_by_order.len(),
                record_count * RECORD_BYTES
            ),
        )?;

        Ok(())
    }
}

#[cfg(feature = "compressed-step-metadata")]
fn main() -> std::io::Result<()> {
    compressed::build()
}

#[cfg(not(feature = "compressed-step-metadata"))]
fn main() {
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_COMPRESSED_STEP_METADATA");
}
