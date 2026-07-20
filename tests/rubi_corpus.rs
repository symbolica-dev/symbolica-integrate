use std::any::Any;
use std::fs;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
    mpsc,
};
use std::thread;
use std::time::{Duration, Instant};
use symbolica::domains::float::Complex;
use symbolica::prelude::*;
use symbolica_integrate::{IntegralFunctions, integrate_with_abort_impl, rubi_differentiate};

const CORPUS_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/RUBITestFiles");
const INDEPENDENT_TEST_SUITE_DIR: &str = "0 Independent test suites";
const EXPECTED_INPUT_FILES: usize = 213;
const EXPECTED_CASES: usize = 72_944;
const CORPUS_CASE_TIMEOUT: Duration = Duration::from_secs(20);
const RUBI_FILE_ENV: &str = "RUBI_FILE";
const RUBI_TRACE_FAILURES_ENV: &str = "RUBI_TRACE_FAILURES";
const RUBI_TRACE_OUTPUT_DIR_ENV: &str = "RUBI_TRACE_OUTPUT_DIR";
const RUBI_TRACE_TIMEOUT_ENV: &str = "RUBI_TRACE_TIMEOUT";
const RUBI_MATHEMATICA_RUBI_ROOT_ENV: &str = "RUBI_MATHEMATICA_RUBI_ROOT";
const RUBI_FAILURE_BACKLOG_ENV: &str = "RUBI_FAILURE_BACKLOG";
const RUBI_SKIP_DERIVATIVE_CHECK_ENV: &str = "RUBI_SKIP_DERIVATIVE_CHECK";
const RUBI_CASE_TIMEOUT_ENV: &str = "RUBI_CASE_TIMEOUT";
const RUBI_EXECUTION_MODE_ENV: &str = "RUBI_EXECUTION_MODE";
const RUBI_ISOLATE_CASES_ENV: &str = "RUBI_ISOLATE_CASES";
const RUBI_CORPUS_ROOT_ENV: &str = "RUBI_CORPUS_ROOT";
const RUBI_CORPUS_WORKER_ENV: &str = "RUBI_CORPUS_WORKER";
const RUBI_CORPUS_WORKER_OUTCOME_PREFIX: &str = "RUBI_CORPUS_WORKER_OUTCOME\t";
const RUBI_SHARD_INDEX_ENV: &str = "RUBI_SHARD_INDEX";
const RUBI_SHARD_COUNT_ENV: &str = "RUBI_SHARD_COUNT";
const RUBI_SLOWEST_COUNT_ENV: &str = "RUBI_SLOWEST_COUNT";
const RUBI_CORPUS_QUIET_ENV: &str = "RUBI_CORPUS_QUIET";
const RUBI_REPORT_ALL_TIMINGS_ENV: &str = "RUBI_REPORT_ALL_TIMINGS";

#[derive(Debug)]
struct Case {
    file: PathBuf,
    line: usize,
    integrand: String,
    variable: String,
    integral_functions: IntegralFunctionSupport,
    expected_rubi_deferred: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum IntegralFunctionSupport {
    Known,
    Unknown(Vec<String>),
}

enum Outcome {
    Unsupported(String),
    RubiDeferred(String),
    Rootsum(String),
    OpaqueSpecial(String),
    Inconclusive(String),
    TimedOut(String),
    Ok,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CorpusExecutionMode {
    Serial,
    AbortWatchdog,
    Isolated,
}

impl CorpusExecutionMode {
    fn parse(value: &str) -> Self {
        match value {
            "serial" => Self::Serial,
            "abort" => Self::AbortWatchdog,
            "isolated" => Self::Isolated,
            _ => panic!("{RUBI_EXECUTION_MODE_ENV} must be one of serial, abort, or isolated"),
        }
    }
}

impl IntegralFunctionSupport {
    fn uses_unknown_functions(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }
}

#[test]
fn rubi_corpus_is_complete() {
    let corpus_root = corpus_root();
    let files = input_files(&corpus_root);
    assert_eq!(
        files.len(),
        EXPECTED_INPUT_FILES,
        "unexpected corpus file count"
    );

    let case_count = files.iter().flat_map(|path| cases_in_file(path)).count();
    assert_eq!(case_count, EXPECTED_CASES, "unexpected corpus case count");
}

#[test]
fn detects_purely_rational_corpus_inputs() {
    let x = symbol!("x");
    assert!(is_purely_rational_in(
        &parse!("(x*d+c+x^2*e+x^3*f+x^4*g+x^5*h+x^6*i+x^7*j)/(a+x^4*b)^4"),
        x,
    ));
    assert!(!is_purely_rational_in(&parse!("sqrt(1+x^2)"), x));
    assert!(!is_purely_rational_in(&parse!("sin(x)/(1+x)"), x));
}

#[test]
fn failure_backlog_json_escapes_control_characters() {
    assert_eq!(json_escape("a\"b\\c\n\t"), "a\\\"b\\\\c\\n\\t");
}

#[test]
fn expected_unintegrable_result_is_rubi_deferred() {
    assert!(expected_rubi_deferred(
        "Unintegrable(1/(x*log(c*(a+b*x^2)^p)),x)"
    ));
    assert!(expected_rubi_deferred(
        "x-2*Unintegrable(log(x)^2/(1+x^2),x)"
    ));
    assert!(expected_rubi_deferred(
        "x-2*CannotIntegrate(log(x)^2/(1+x^2),x)"
    ));
    assert!(!expected_rubi_deferred("log(x)"));
}

#[test]
fn parses_corpus_execution_modes() {
    assert_eq!(
        CorpusExecutionMode::parse("serial"),
        CorpusExecutionMode::Serial
    );
    assert_eq!(
        CorpusExecutionMode::parse("abort"),
        CorpusExecutionMode::AbortWatchdog
    );
    assert_eq!(
        CorpusExecutionMode::parse("isolated"),
        CorpusExecutionMode::Isolated
    );
}

#[test]
#[ignore = "the complete Rubi corpus is intentionally opt-in; run with --ignored"]
fn rubi_corpus_integrals_round_trip() {
    let config = CorpusConfig::from_env();
    if env_flag(RUBI_CORPUS_WORKER_ENV) {
        run_corpus_case_worker(config);
        return;
    }

    run_corpus_cases_direct(config);
}

#[derive(Debug)]
struct CorpusConfig {
    sample_stride: Option<usize>,
    shard_index: Option<usize>,
    shard_count: Option<usize>,
    skip_rational: bool,
    only_independent: bool,
    file_filter: Option<String>,
    file_exact: Option<PathBuf>,
    line_filter: Option<usize>,
    include_unknown_functions: bool,
    trace_failures: bool,
    trace_output_dir: PathBuf,
    trace_timeout_seconds: u64,
    mathematica_rubi_root: PathBuf,
    failure_backlog: Option<PathBuf>,
    skip_derivative_check: bool,
    case_timeout: Duration,
    execution_mode: CorpusExecutionMode,
    slowest_count: usize,
    quiet: bool,
    report_all_timings: bool,
}

impl CorpusConfig {
    fn from_env() -> Self {
        // Optional: set RUBI_SAMPLE=N to test only every Nth case (e.g. RUBI_SAMPLE=100).
        let sample_stride = std::env::var("RUBI_SAMPLE")
            .ok()
            .map(|v| v.parse().expect("RUBI_SAMPLE must be a positive integer"));
        let shard_count = std::env::var(RUBI_SHARD_COUNT_ENV).ok().map(|v| {
            v.parse()
                .expect("RUBI_SHARD_COUNT must be a positive integer")
        });
        let shard_index = std::env::var(RUBI_SHARD_INDEX_ENV).ok().map(|v| {
            v.parse()
                .expect("RUBI_SHARD_INDEX must be a nonnegative integer")
        });
        match (shard_index, shard_count) {
            (Some(index), Some(count)) if count > 0 && index < count => {}
            (None, None) => {}
            _ => {
                panic!("RUBI_SHARD_INDEX and RUBI_SHARD_COUNT must both be set with index < count")
            }
        }
        // Optional: set RUBI_SKIP_RATIONAL=1 to avoid pure rational cases that may hit
        // expensive Trager integration in Symbolica.
        let skip_rational = env_flag("RUBI_SKIP_RATIONAL");
        // Optional: set RUBI_ONLY_INDEPENDENT=1 to test only the independent
        // Rubi suite examples under "0 Independent test suites".
        let only_independent = env_flag("RUBI_ONLY_INDEPENDENT");
        // Optional: set RUBI_FILE_CONTAINS=text to test only corpus input files
        // whose path contains the given text.
        let file_filter = std::env::var("RUBI_FILE_CONTAINS").ok();
        // Internal: set RUBI_FILE=path to test only one exact corpus file.
        let file_exact = std::env::var(RUBI_FILE_ENV).ok().map(PathBuf::from);
        // Optional: set RUBI_LINE=N to test only the case on line N of each
        // selected input file.
        let line_filter = std::env::var("RUBI_LINE")
            .ok()
            .map(|v| v.parse().expect("RUBI_LINE must be a positive integer"));
        // Optional: set RUBI_INCLUDE_UNKNOWN_FUNCTIONS=1 to also test cases whose Rubi
        // reference primitive uses functions not implemented by Symbolica.
        let include_unknown_functions = env_flag("RUBI_INCLUDE_UNKNOWN_FUNCTIONS");
        // Optional: set RUBI_TRACE_FAILURES=1 to run Mathematica/Rubi tracing only
        // for cases that fail in this Rust corpus run.
        let trace_failures = env_flag(RUBI_TRACE_FAILURES_ENV);
        // Optional: where RUBI_TRACE_FAILURES writes traces.
        let trace_output_dir = std::env::var(RUBI_TRACE_OUTPUT_DIR_ENV)
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from("/tmp/rubi_traces"));
        // Optional: timeout in seconds for each Mathematica/Rubi trace.
        let trace_timeout_seconds = std::env::var(RUBI_TRACE_TIMEOUT_ENV)
            .ok()
            .map(|v| {
                v.parse()
                    .expect("RUBI_TRACE_TIMEOUT must be a positive integer")
            })
            .unwrap_or(180);
        let mathematica_rubi_root = std::env::var(RUBI_MATHEMATICA_RUBI_ROOT_ENV)
            .map(PathBuf::from)
            .unwrap_or_else(|_| {
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("vendor")
                    .join("Rubi-4.17.3.0")
            });
        let failure_backlog = std::env::var(RUBI_FAILURE_BACKLOG_ENV)
            .ok()
            .map(PathBuf::from);
        let skip_derivative_check = env_flag(RUBI_SKIP_DERIVATIVE_CHECK_ENV);
        // Optional: wall-clock timeout for each corpus case, including derivative
        // verification when process isolation is enabled.
        let case_timeout = Duration::from_secs(
            std::env::var(RUBI_CASE_TIMEOUT_ENV)
                .ok()
                .map(|v| {
                    v.parse()
                        .expect("RUBI_CASE_TIMEOUT must be a positive integer")
                })
                .unwrap_or(CORPUS_CASE_TIMEOUT.as_secs()),
        );
        // `serial` removes both subprocess and watchdog-thread startup from
        // trusted sweeps. `isolated` remains the only mode that can forcibly
        // stop code which does not observe the integration abort flag.
        let execution_mode = std::env::var(RUBI_EXECUTION_MODE_ENV)
            .ok()
            .map(|value| CorpusExecutionMode::parse(&value))
            .unwrap_or_else(|| {
                let isolate_cases = std::env::var(RUBI_ISOLATE_CASES_ENV)
                    .ok()
                    .map(|value| env_value_enabled(&value))
                    .unwrap_or_else(|| {
                        file_filter.is_some()
                            || file_exact.is_some()
                            || line_filter.is_some()
                            || sample_stride.is_some()
                            || shard_index.is_some()
                    });
                if isolate_cases {
                    CorpusExecutionMode::Isolated
                } else {
                    CorpusExecutionMode::AbortWatchdog
                }
            });
        let slowest_count = std::env::var(RUBI_SLOWEST_COUNT_ENV)
            .ok()
            .map(|value| {
                value
                    .parse()
                    .expect("RUBI_SLOWEST_COUNT must be a nonnegative integer")
            })
            .unwrap_or(0);
        let quiet = env_flag(RUBI_CORPUS_QUIET_ENV);
        let report_all_timings = env_flag(RUBI_REPORT_ALL_TIMINGS_ENV);

        Self {
            sample_stride,
            shard_index,
            shard_count,
            skip_rational,
            only_independent,
            file_filter,
            file_exact,
            line_filter,
            include_unknown_functions,
            trace_failures,
            trace_output_dir,
            trace_timeout_seconds,
            mathematica_rubi_root,
            failure_backlog,
            skip_derivative_check,
            case_timeout,
            execution_mode,
            slowest_count,
            quiet,
            report_all_timings,
        }
    }

    fn suite_note(&self) -> &'static str {
        if self.only_independent {
            " independent suites"
        } else {
            ""
        }
    }

    fn sample_note(&self) -> String {
        let sample = self
            .sample_stride
            .map(|stride| format!(" (sampled every {stride} cases)"))
            .unwrap_or_default();
        let shard = self
            .shard_index
            .zip(self.shard_count)
            .map(|(index, count)| format!(" (shard {index}/{count})"))
            .unwrap_or_default();
        format!("{sample}{shard}")
    }

    fn file_filter_note(&self) -> String {
        self.file_filter
            .as_ref()
            .map(|filter| format!(" filtered by {filter:?}"))
            .unwrap_or_default()
    }
}

fn run_corpus_cases_direct(config: CorpusConfig) {
    let mut parsed = 0usize;
    let mut skipped_rational = 0usize;
    let mut skipped_unknown_functions = 0usize;
    let mut unsupported = 0usize;
    let mut rubi_deferred = 0usize;
    let mut rootsums = 0usize;
    let mut opaque_specials = 0usize;
    let mut inconclusive = 0usize;
    let mut timeouts = 0usize;
    let mut panics = 0usize;
    let mut failures = Vec::new();
    let mut slowest = Vec::new();
    let mut timings = Vec::new();
    let mut current_file: Option<PathBuf> = None;

    for (_index, case) in selected_cases(&config) {
        if !config.skip_derivative_check
            && !config.include_unknown_functions
            && !case.expected_rubi_deferred
            && case.integral_functions.uses_unknown_functions()
        {
            skipped_unknown_functions += 1;
            continue;
        }

        let integrand = parse_case_expression(&case, &case.integrand);

        if !config.quiet && current_file.as_ref() != Some(&case.file) {
            println!(
                "{}",
                case.file.file_name().unwrap_or_default().to_string_lossy()
            );
            current_file = Some(case.file.clone());
        }
        if !config.quiet {
            println!("{} {}", case.line, case.integrand,);
        }

        let variable = Symbol::parse(&case.variable, "rubi_corpus").unwrap_or_else(|error| {
            panic!(
                "{}:{}: invalid variable {}: {error}",
                case.file.display(),
                case.line,
                case.variable
            )
        });
        if config.skip_rational && is_purely_rational_in(&integrand, variable) {
            skipped_rational += 1;
            continue;
        }

        parsed += 1;

        let integration_started = Instant::now();
        let result = match config.execution_mode {
            CorpusExecutionMode::Serial => run_case_serial(
                &case,
                &integrand,
                variable,
                config.case_timeout,
                config.skip_derivative_check,
            ),
            CorpusExecutionMode::AbortWatchdog => run_case_checked(
                &case,
                &integrand,
                variable,
                config.case_timeout,
                config.skip_derivative_check,
            ),
            CorpusExecutionMode::Isolated => run_case_in_subprocess(&config, &case),
        };
        let integration_elapsed = integration_started.elapsed();
        record_slow_integration(
            &mut slowest,
            config.slowest_count,
            integration_elapsed,
            &case,
        );
        timings.push(integration_elapsed);
        if config.report_all_timings {
            println!(
                "RUBI_INTEGRATION_TIMING\t{:.9}",
                integration_elapsed.as_secs_f64()
            );
        }

        match result {
            Err(payload) => {
                panics += 1;
                let panic_message = panic_payload_message(payload.as_ref());
                append_failure_backlog(&config, &case, "panic", &panic_message);
                let trace_note = failure_trace_note(&config, &case);
                record_failure(
                    &mut failures,
                    format!(
                        "{}:{}: panic while integrating {}\npanic: {}\n{}",
                        case.file.display(),
                        case.line,
                        case.integrand,
                        panic_message,
                        trace_note,
                    ),
                );
            }
            Ok(Outcome::Unsupported(msg)) => {
                unsupported += 1;
                append_failure_backlog(&config, &case, "unsupported", &msg);
                record_failure(&mut failures, with_failure_trace_note(&config, &case, msg));
            }
            Ok(Outcome::RubiDeferred(msg)) => {
                rubi_deferred += 1;
                if !config.quiet {
                    println!("{msg}");
                }
            }
            Ok(Outcome::Rootsum(msg)) => {
                rootsums += 1;
                if !config.quiet {
                    println!("{msg}");
                }
            }
            Ok(Outcome::OpaqueSpecial(msg)) => {
                opaque_specials += 1;
                append_failure_backlog(&config, &case, "derivative_unverifiable_special", &msg);
            }
            Ok(Outcome::Inconclusive(msg)) => {
                inconclusive += 1;
                append_failure_backlog(&config, &case, "inconclusive", &msg);
                record_failure(&mut failures, with_failure_trace_note(&config, &case, msg));
            }
            Ok(Outcome::TimedOut(msg)) => {
                timeouts += 1;
                append_failure_backlog(&config, &case, "timed_out", &msg);
                record_failure(&mut failures, with_failure_trace_note(&config, &case, msg));
            }
            Ok(Outcome::Ok) => {}
        }
    }

    let suite_note = config.suite_note();
    let sample_note = config.sample_note();
    let file_filter_note = config.file_filter_note();
    assert!(
        parsed > 0
            || skipped_unknown_functions > 0
            || (config.skip_rational && skipped_rational > 0),
        "Rubi corpus{suite_note}{sample_note}{file_filter_note}: no cases were selected"
    );
    let summary = format!(
        "Rubi corpus{suite_note}{sample_note}{file_filter_note}: parsed {parsed}, skipped rational {skipped_rational}, skipped unknown-function primitives {skipped_unknown_functions}, unsupported {unsupported}, Rubi-deferred {rubi_deferred}, opaque rootsum primitives {rootsums}, derivative unverifiable (special functions) {opaque_specials}, failed derivative zero checks {inconclusive}, timeouts {timeouts}, panics {panics}."
    );
    for timing in &slowest {
        println!(
            "RUBI_SLOW_INTEGRATION\t{:.6}\t{}:{}\t{}",
            timing.elapsed.as_secs_f64(),
            timing.file.display(),
            timing.line,
            timing.integrand,
        );
    }
    timings.sort_unstable();
    let total_seconds: f64 = timings.iter().map(Duration::as_secs_f64).sum();
    let average_seconds = total_seconds / timings.len() as f64;
    let median_seconds = if timings.len() % 2 == 0 {
        (timings[timings.len() / 2 - 1].as_secs_f64() + timings[timings.len() / 2].as_secs_f64())
            / 2.0
    } else {
        timings[timings.len() / 2].as_secs_f64()
    };
    let max_seconds = timings
        .last()
        .expect("a nonempty corpus selection has timings")
        .as_secs_f64();
    println!(
        "RUBI_TIMING_SUMMARY\t{}\t{total_seconds:.9}\t{average_seconds:.9}\t{median_seconds:.9}\t{max_seconds:.9}",
        timings.len()
    );
    println!("{summary}");
    assert!(
        failures.is_empty(),
        "{summary} First failures:\n{}",
        failures.join("\n\n"),
    );
}

#[derive(Debug)]
struct SlowIntegration {
    elapsed: Duration,
    file: PathBuf,
    line: usize,
    integrand: String,
}

fn record_slow_integration(
    slowest: &mut Vec<SlowIntegration>,
    limit: usize,
    elapsed: Duration,
    case: &Case,
) {
    if limit == 0
        || (slowest.len() == limit
            && slowest
                .last()
                .is_some_and(|timing| elapsed <= timing.elapsed))
    {
        return;
    }

    slowest.push(SlowIntegration {
        elapsed,
        file: case.file.clone(),
        line: case.line,
        integrand: case.integrand.clone(),
    });
    slowest.sort_unstable_by(|left, right| right.elapsed.cmp(&left.elapsed));
    slowest.truncate(limit);
}

fn run_case_serial(
    case: &Case,
    integrand: &Atom,
    variable: Symbol,
    case_timeout: Duration,
    skip_derivative_check: bool,
) -> Result<Outcome, Box<dyn Any + Send>> {
    let abort = AtomicBool::new(false);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_case_body(
            case,
            integrand,
            variable,
            &abort,
            case_timeout,
            skip_derivative_check,
        )
    }))
}

fn run_case_checked(
    case: &Case,
    integrand: &Atom,
    variable: Symbol,
    case_timeout: Duration,
    skip_derivative_check: bool,
) -> Result<Outcome, Box<dyn Any + Send>> {
    let abort = Arc::new(AtomicBool::new(false));
    let (watchdog_done, watchdog_done_rx) = mpsc::channel();
    let watchdog_abort = Arc::clone(&abort);
    let watchdog = thread::spawn(move || {
        if watchdog_done_rx.recv_timeout(case_timeout).is_err() {
            watchdog_abort.store(true, Ordering::Relaxed);
        }
    });

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_case_body(
            case,
            integrand,
            variable,
            &abort,
            case_timeout,
            skip_derivative_check,
        )
    }));

    let _ = watchdog_done.send(());
    watchdog
        .join()
        .expect("corpus timeout watchdog should not panic");

    result
}

fn run_case_body(
    case: &Case,
    integrand: &Atom,
    variable: Symbol,
    abort: &AtomicBool,
    case_timeout: Duration,
    skip_derivative_check: bool,
) -> Outcome {
    let antiderivative = match integrate_with_abort_impl(integrand, variable, abort) {
        Some(Ok(antiderivative)) => antiderivative,
        None => {
            return Outcome::TimedOut(format!(
                "{}:{}: timed out after {} seconds while integrating {}",
                case.file.display(),
                case.line,
                case_timeout.as_secs(),
                case.integrand,
            ));
        }
        Some(Err(_)) => {
            if known_rubi_deferred_case(case) {
                return Outcome::RubiDeferred(format!(
                    "{}:{}: Mathematica Rubi returns deferred Int for {}",
                    case.file.display(),
                    case.line,
                    case.integrand,
                ));
            }
            return Outcome::Unsupported(format!(
                "{}:{}: no antiderivative for {}",
                case.file.display(),
                case.line,
                case.integrand,
            ));
        }
    };

    if antiderivative.to_string() == "⧞" || contains_unintegrable(&antiderivative) {
        if known_rubi_deferred_case(case) {
            return Outcome::RubiDeferred(format!(
                "{}:{}: Mathematica Rubi returns deferred Int for {}",
                case.file.display(),
                case.line,
                case.integrand,
            ));
        }
        return Outcome::Unsupported(format!(
            "{}:{}: indeterminate primitive for {}",
            case.file.display(),
            case.line,
            case.integrand,
        ));
    }

    if antiderivative.to_string().contains("rootsum(") {
        // `rootsum` is currently an interim opaque node, so Symbolica cannot
        // differentiate it to verify the round trip yet.
        return Outcome::Rootsum(format!(
            "{}:{}: opaque rootsum primitive for {}",
            case.file.display(),
            case.line,
            case.integrand,
        ));
    }

    let special_function_heads = rubi_special_function_heads(&antiderivative);
    if skip_derivative_check && !special_function_heads.is_empty() {
        // Rubi may legitimately return special-function primitives whose
        // derivative requires identities that Symbolica's local verifier cannot
        // yet prove.
        return Outcome::OpaqueSpecial(format!(
            "{}:{}: derivative unverifiable because of special functions [{}] for {}\nprimitive: {}",
            case.file.display(),
            case.line,
            special_function_heads.join(", "),
            case.integrand,
            antiderivative,
        ));
    }

    if skip_derivative_check {
        return Outcome::Ok;
    }

    let verification_integrand = normalize_log_exp_for_verification(integrand);
    let raw_residual = normalize_deferred_rubi_integral_derivatives(
        &normalize_trig_radicals_for_verification(&normalize_pi_half_trig_for_verification(
            &normalize_log_exp_for_verification(
                &(rubi_differentiate(&antiderivative, variable) - verification_integrand),
            ),
        )),
        variable,
    );
    let residual = if residual_is_zero(&raw_residual) {
        raw_residual.clone()
    } else {
        cancel_for_verification(&raw_residual).unwrap_or_else(|| raw_residual.clone())
    };
    let residual = if residual_is_zero(&residual) {
        residual
    } else {
        let expanded = raw_residual.expand();
        cancel_for_verification(&expanded).unwrap_or(expanded)
    };
    let residual = if residual_is_zero(&residual) {
        residual
    } else {
        residual.factor()
    };
    if !residual_is_zero(&residual) {
        if !special_function_heads.is_empty() {
            return Outcome::OpaqueSpecial(format!(
                "{}:{}: derivative unverifiable because of special functions [{}] for {}\nprimitive: {}\nresidual: {}",
                case.file.display(),
                case.line,
                special_function_heads.join(", "),
                case.integrand,
                antiderivative,
                residual,
            ));
        }
        return Outcome::Inconclusive(format!(
            "{}:{}: derivative round trip failed for {}\nprimitive: {}\nresidual: {}",
            case.file.display(),
            case.line,
            case.integrand,
            antiderivative,
            residual,
        ));
    }

    Outcome::Ok
}

fn run_corpus_case_worker(config: CorpusConfig) {
    let cases = selected_cases(&config);
    let [(_index, case)] = cases.as_slice() else {
        println!(
            "{RUBI_CORPUS_WORKER_OUTCOME_PREFIX}panic\t{}",
            encode_worker_message(&format!(
                "worker expected exactly one selected case, got {}",
                cases.len()
            ))
        );
        return;
    };

    let integrand = parse_case_expression(case, &case.integrand);
    let variable = Symbol::parse(&case.variable, "rubi_corpus").unwrap_or_else(|error| {
        panic!(
            "{}:{}: invalid variable {}: {error}",
            case.file.display(),
            case.line,
            case.variable
        )
    });
    let result = run_case_checked(
        case,
        &integrand,
        variable,
        config.case_timeout,
        config.skip_derivative_check,
    );
    print_worker_result(result);
}

fn run_case_in_subprocess(
    config: &CorpusConfig,
    case: &Case,
) -> Result<Outcome, Box<dyn Any + Send>> {
    let mut child = Command::new(std::env::current_exe().expect("test binary path is available"))
        .arg("rubi_corpus_integrals_round_trip")
        .arg("--exact")
        .arg("--ignored")
        .arg("--nocapture")
        .env(RUBI_CORPUS_WORKER_ENV, "1")
        .env(RUBI_FILE_ENV, &case.file)
        .env("RUBI_LINE", case.line.to_string())
        .env("RUBI_INCLUDE_UNKNOWN_FUNCTIONS", "1")
        .env(
            RUBI_CASE_TIMEOUT_ENV,
            config.case_timeout.as_secs().to_string(),
        )
        .env_remove("RUBI_SAMPLE")
        .env_remove("RUBI_FILE_CONTAINS")
        .env_remove("RUBI_ONLY_INDEPENDENT")
        .env_remove(RUBI_SHARD_INDEX_ENV)
        .env_remove(RUBI_SHARD_COUNT_ENV)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("corpus worker should start");

    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_status)) => break,
            Ok(None) if start.elapsed() >= config.case_timeout => {
                let _ = child.kill();
                let output = child
                    .wait_with_output()
                    .expect("timed-out corpus worker output should be available");
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                return Ok(Outcome::TimedOut(format!(
                    "{}:{}: timed out after {} seconds while processing {} (integration or derivative verification)\nworker stdout:\n{}\nworker stderr:\n{}",
                    case.file.display(),
                    case.line,
                    config.case_timeout.as_secs(),
                    case.integrand,
                    stdout.trim(),
                    stderr.trim(),
                )));
            }
            Ok(None) => thread::sleep(Duration::from_millis(25)),
            Err(error) => panic!("could not poll corpus worker: {error}"),
        }
    }

    let output = child
        .wait_with_output()
        .expect("completed corpus worker output should be available");
    parse_worker_result(
        case,
        output.status.success(),
        &output.stdout,
        &output.stderr,
    )
}

fn print_worker_result(result: Result<Outcome, Box<dyn Any + Send>>) {
    let (kind, message) = match result {
        Err(payload) => ("panic", panic_payload_message(payload.as_ref())),
        Ok(Outcome::Unsupported(message)) => ("unsupported", message),
        Ok(Outcome::RubiDeferred(message)) => ("rubi_deferred", message),
        Ok(Outcome::Rootsum(message)) => ("rootsum", message),
        Ok(Outcome::OpaqueSpecial(message)) => ("opaque_special", message),
        Ok(Outcome::Inconclusive(message)) => ("inconclusive", message),
        Ok(Outcome::TimedOut(message)) => ("timed_out", message),
        Ok(Outcome::Ok) => ("ok", String::new()),
    };
    println!(
        "{RUBI_CORPUS_WORKER_OUTCOME_PREFIX}{kind}\t{}",
        encode_worker_message(&message)
    );
}

fn parse_worker_result(
    case: &Case,
    success: bool,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<Outcome, Box<dyn Any + Send>> {
    let stdout = String::from_utf8_lossy(stdout);
    let stderr = String::from_utf8_lossy(stderr);
    if !stderr.trim().is_empty() {
        eprintln!(
            "{}:{}: corpus worker stderr while processing {}:\n{}",
            case.file.display(),
            case.line,
            case.integrand,
            stderr.trim(),
        );
    }
    for line in stdout.lines() {
        let Some(rest) = line.strip_prefix(RUBI_CORPUS_WORKER_OUTCOME_PREFIX) else {
            continue;
        };
        let Some((kind, message)) = rest.split_once('\t') else {
            break;
        };
        let message = decode_worker_message(message);
        return match kind {
            "ok" => Ok(Outcome::Ok),
            "unsupported" => Ok(Outcome::Unsupported(message)),
            "rubi_deferred" => Ok(Outcome::RubiDeferred(message)),
            "rootsum" => Ok(Outcome::Rootsum(message)),
            "opaque_special" => Ok(Outcome::OpaqueSpecial(message)),
            "inconclusive" => Ok(Outcome::Inconclusive(message)),
            "timed_out" => Ok(Outcome::TimedOut(message)),
            "panic" => Err(Box::new(message)),
            _ => Err(Box::new(format!("unknown corpus worker outcome {kind:?}"))),
        };
    }

    Err(Box::new(format!(
        "{}:{}: corpus worker exited without a parseable outcome marker (success: {success})\nstdout:\n{}\nstderr:\n{}",
        case.file.display(),
        case.line,
        stdout.trim(),
        stderr.trim(),
    )))
}

fn selected_cases(config: &CorpusConfig) -> Vec<(usize, Case)> {
    let mut selected = Vec::new();
    let mut global_index = 0usize;
    for path in selected_files(config) {
        for case in cases_in_file(&path) {
            let index = global_index;
            global_index += 1;
            if let Some(line) = config.line_filter
                && case.line != line
            {
                continue;
            }
            if let Some(stride) = config.sample_stride
                && index % stride != 0
            {
                continue;
            }
            if let Some((shard_index, shard_count)) = config.shard_index.zip(config.shard_count)
                && index % shard_count != shard_index
            {
                continue;
            }
            selected.push((index, case));
        }
    }

    selected
}

fn selected_files(config: &CorpusConfig) -> Vec<PathBuf> {
    let corpus_root = corpus_root();
    let mut files = input_files(&corpus_root);
    if config.only_independent {
        files.retain(|path| is_independent_suite_file(path));
    }
    if let Some(filter) = &config.file_filter {
        files.retain(|path| path.to_string_lossy().contains(filter));
    }
    if let Some(exact) = &config.file_exact {
        let exact = if exact.is_absolute() {
            exact.clone()
        } else {
            Path::new(env!("CARGO_MANIFEST_DIR")).join(exact)
        };
        files.retain(|path| path == &exact);
    }

    files
}

fn corpus_root() -> PathBuf {
    std::env::var(RUBI_CORPUS_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(CORPUS_ROOT))
}

fn is_independent_suite_file(path: &Path) -> bool {
    path.components()
        .any(|component| component.as_os_str() == INDEPENDENT_TEST_SUITE_DIR)
}

fn env_flag(name: &str) -> bool {
    std::env::var(name).is_ok_and(|value| env_value_enabled(&value))
}

fn env_value_enabled(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn encode_worker_message(message: &str) -> String {
    message
        .replace('%', "%25")
        .replace('\t', "%09")
        .replace('\r', "%0D")
        .replace('\n', "%0A")
}

fn decode_worker_message(message: &str) -> String {
    let mut decoded = String::with_capacity(message.len());
    let mut chars = message.chars();
    while let Some(ch) = chars.next() {
        if ch != '%' {
            decoded.push(ch);
            continue;
        }

        let first = chars.next();
        let second = chars.next();
        match (first, second) {
            (Some('2'), Some('5')) => decoded.push('%'),
            (Some('0'), Some('9')) => decoded.push('\t'),
            (Some('0'), Some('D')) => decoded.push('\r'),
            (Some('0'), Some('A')) => decoded.push('\n'),
            (Some(first), Some(second)) => {
                decoded.push('%');
                decoded.push(first);
                decoded.push(second);
            }
            (Some(first), None) => {
                decoded.push('%');
                decoded.push(first);
            }
            (None, _) => decoded.push('%'),
        }
    }
    decoded
}

fn is_purely_rational_in(expr: &Atom, x: Symbol) -> bool {
    let Some(Ok(rational)): Option<Result<RationalPolynomial<IntegerRing, u16>, _>> =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            expr.clone().try_to_rational_polynomial(&Q, &Z, x)
        }))
        .ok()
    else {
        return false;
    };

    rational
        .get_variables()
        .iter()
        .all(|variable| match variable {
            PolyVariable::Symbol(_) => true,
            PolyVariable::Function(_, atom) | PolyVariable::Power(atom) => !atom.contains_symbol(x),
            PolyVariable::Temporary(_) => false,
        })
}

fn record_failure(failures: &mut Vec<String>, failure: String) {
    println!("\tFailure: {failure}");
    const MAX_REPORTED_FAILURES: usize = 10;
    if failures.len() < MAX_REPORTED_FAILURES {
        failures.push(failure);
    }
}

fn append_failure_backlog(config: &CorpusConfig, case: &Case, outcome: &str, message: &str) {
    let Some(path) = &config.failure_backlog else {
        return;
    };
    if let Some(parent) = path.parent()
        && let Err(error) = fs::create_dir_all(parent)
    {
        eprintln!(
            "could not create failure backlog directory {}: {error}",
            parent.display()
        );
        return;
    }

    let trace_path = config.trace_failures.then(|| {
        config
            .trace_output_dir
            .join(format!("{}.txt", rubi_trace_filename(case)))
    });
    let trace_json = trace_path
        .as_ref()
        .map(|path| format!("\"{}\"", json_escape(&path.display().to_string())))
        .unwrap_or_else(|| "null".to_owned());
    let record = format!(
        "{{\"outcome\":\"{}\",\"file\":\"{}\",\"line\":{},\"integrand\":\"{}\",\"message\":\"{}\",\"rubi_source_release\":\"4.17.3.0\",\"trace\":{}}}\n",
        json_escape(outcome),
        json_escape(&case.file.display().to_string()),
        case.line,
        json_escape(&case.integrand),
        json_escape(message),
        trace_json,
    );
    match OpenOptions::new().create(true).append(true).open(path) {
        Ok(mut file) => {
            if let Err(error) = file.write_all(record.as_bytes()) {
                eprintln!(
                    "could not append failure backlog {}: {error}",
                    path.display()
                );
            }
        }
        Err(error) => eprintln!("could not open failure backlog {}: {error}", path.display()),
    }
}

fn json_escape(value: &str) -> String {
    value
        .chars()
        .flat_map(|ch| match ch {
            '\\' => "\\\\".chars().collect::<Vec<_>>(),
            '"' => "\\\"".chars().collect(),
            '\n' => "\\n".chars().collect(),
            '\r' => "\\r".chars().collect(),
            '\t' => "\\t".chars().collect(),
            ch if ch.is_control() => format!("\\u{:04x}", ch as u32).chars().collect(),
            ch => vec![ch],
        })
        .collect()
}

fn known_rubi_deferred_case(case: &Case) -> bool {
    if case.expected_rubi_deferred {
        return true;
    }

    let Some(file_name) = case.file.file_name().and_then(|name| name.to_str()) else {
        return false;
    };

    matches!(
        (file_name, case.line),
        // Mathematica Rubi applies NormalizeIntegrand/ExpandIntegrand
        // rules 7292 and 7293, then leaves four deferred inner Int terms.
        ("Bronstein Problems.input", 21)
            // Latest Rubi expands the sum and applies DownValues 2691, 2692,
            // and 2703, but the resulting power integrals remain deferred.
            | ("Bronstein Problems.input", 19)
            // Latest Rubi applies only terminal DownValue 7299 to these
            // unnormalized cubic-exponential inputs.
            | ("2.3 Exponential functions.input", 239)
            | ("2.3 Exponential functions.input", 240)
            | ("2.3 Exponential functions.input", 241)
            | ("2.3 Exponential functions.input", 242)
            | ("2.3 Exponential functions.input", 243)
            // Latest Rubi applies only DownValue 2867 and returns Unintegrable
            // for the algebraic multiplier of the logarithm.
            | ("Bondarenko Problems.input", 14)
            | ("Bondarenko Problems.input", 15)
            // Latest Rubi applies no rule and returns Defer[Int] directly.
            | ("Hearn Problems.input", 92)
            | ("Hearn Problems.input", 164)
            // Rubi rule 2720 returns a deferred exponential Subst payload.
            | ("Hearn Problems.input", 195)
            | ("Hearn Problems.input", 326)
            // Int linearity leaves the quartic square-root term deferred.
            | ("Hearn Problems.input", 352)
            // Latest Rubi applies rules 2026 and 7276, expands the rational
            // factor, and leaves the resulting exponential terms deferred.
            | ("Hebisch Problems.input", 11)
            | ("Hebisch Problems.input", 12)
            | ("Charlwood Problems.input", 14)
            | ("Charlwood Problems.input", 140)
            // Mathematica Rubi returns Defer[Int][x*(...), x] after applying
            // integration by parts to the exponential-rational integrand.
            | ("2.3 Exponential functions.input", 66)
            // Mathematica Rubi leaves these reciprocal exponential-cubic
            // cases as Defer[Subst][Defer[Int][...], x, f^x].
            | ("2.3 Exponential functions.input", 78)
            | ("2.3 Exponential functions.input", 79)
            // Mathematica Rubi expands these integration-competition x^x
            // cases and returns integration-by-parts expressions containing
            // deferred inner Int terms, despite the corpus listing elementary
            // primitives.
            | ("2.3 Exponential functions.input", 805)
            | ("2.3 Exponential functions.input", 807)
            // Current Rubi 4.17.3 applies only rules {7292,7299} to line 50.
            // For line 54 it applies {27,7292,7293,2009,7299,...} and returns
            // a linear combination of three deferred trigonometric integrals.
            | ("4.7.6 f^(a+b x+c x^2) trig(d+e x+f x^2)^n.input", 50)
            | ("4.7.6 f^(a+b x+c x^2) trig(d+e x+f x^2)^n.input", 54)
            // Latest Rubi terminates these sine recurrences at DownValue 3404
            // and returns a deferred inner Int rather than the corpus result.
            | ("4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input", 1884)
            | ("4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input", 1895)
            | ("4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.input", 1952)
            // Latest Rubi deactivates the trig heads with rule 3042, then
            // terminal rules 3211 and 3707 return Unintegrable.
            | ("4.1.1.3 (g tan)^p (a+b sin)^m.input", 245)
            | ("4.1.1.3 (g tan)^p (a+b sin)^m.input", 246)
            | ("4.1.7 (d trig)^m (a+b (c sin)^n)^p.input", 496)
            | ("4.1.7 (d trig)^m (a+b (c sin)^n)^p.input", 497)
            // Mathematica Rubi applies only source rules and returns deferred
            // inner Int terms: 232 via {27,7293,793,2524}, 331 via
            // {2639,2638,3034,27,3027,7293,3018}, 343 via {7293,7276}, and
            // 346 via {7293}.
            | ("Hearn Problems.input", 232)
            | ("Hearn Problems.input", 331)
            | ("Hearn Problems.input", 343)
            | ("Hearn Problems.input", 346)
            // Mathematica Rubi applies rules 2027 and 7293, then leaves two
            // deferred exponential inner Int terms.
            | ("Hearn Problems.input", 194)
            // Mathematica Rubi applies only DownValue 200 and returns the
            // original four-linear-factor integral deferred.
            | ("1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q.input", 158)
            // Mathematica Rubi applies rules {2463,7293,7266,2635,2639,7276},
            // emits ExpIntegralEi terms, and leaves deferred inner Int terms.
            | ("Hebisch Problems.input", 18)
            | ("Timofeev Problems.input", 315)
            // Mathematica Rubi applies rules 2490 and 2486, then leaves a
            // Defer[Subst][Defer[Int][...], x, ...] result.
            | ("Welz Problems.input", 94)
            // Mathematica Rubi applies rules {6718,1607,133}: the polynomial
            // split yields an AppellF1 term and one deferred four-factor Int.
            | ("Welz Problems.input", 95)
            // Mathematica Rubi applies only rule 6718 and leaves the
            // normalized three-affine-factor Int deferred.
            | ("Welz Problems.input", 96)
            // Mathematica Rubi applies rule 5242 (and its ArcSinh analogue)
            // once, then leaves the integration-by-parts remainder deferred.
            | ("5.1.5 Inverse sine functions.input", 44)
            | ("7.1.5 Inverse hyperbolic sine functions.input", 53)
            // Latest Rubi applies only ExpandIntegrand rule 7293 and leaves
            // the resulting six inner Int terms deferred.
            | ("1.3.2 Algebraic functions.input", 827)
            | ("1.3.2 Algebraic functions.input", 828)
            // Latest Rubi applies only DownValue 7299 and returns Defer[Int]
            // for the general cubic power over its linear factor.
            | ("1.3.2 Algebraic functions.input", 272)
            // Latest Rubi applies only DownValue 1571 and returns Unintegrable
            // for this quartic square-root product.
            | ("1.2.2.3 (d+e x^2)^m (a+b x^2+c x^4)^p.input", 235)
            // Latest Rubi applies no integration rule to these expressions.
            | ("1.3.2 Algebraic functions.input", 1322)
            | ("1.3.2 Algebraic functions.input", 1355)
            // Rubi performs its generic square-root substitution, whose inner
            // integral is the directly deferred line-1322 expression.
            | ("1.3.2 Algebraic functions.input", 1323)
            // Latest Rubi applies linearity and helper rules 7292/7293, then
            // leaves the resulting three logarithmic terms deferred.
            | ("3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.input", 103)
            | ("3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.input", 104)
            // Latest Rubi applies DownValue 2874 and leaves its inner Int
            // deferred for 515; it applies no rule to 516 or 517.
            | ("3.3 u (a+b log(c (d+e x)^n))^p.input", 515)
            | ("3.3 u (a+b log(c (d+e x)^n))^p.input", 516)
            | ("3.3 u (a+b log(c (d+e x)^n))^p.input", 517)
            | ("3.3 u (a+b log(c (d+e x)^n))^p.input", 519)
            // Latest Rubi applies rule 7034 three times, then leaves the
            // resulting ExpIntegralE[0,...] integral deferred.
            | ("8.3 Exponential integral functions.input", 149)
            // Latest Rubi terminates these secant cases in Unintegrable:
            // line 350 via {3042,4365}, line 413 via {3042,4387},
            // line 327 via {3042,4433}, line 153 via {3042,4623}, and
            // line 343 via {3042,4638}.
            | ("4.5.1.3 (d sin)^n (a+b sec)^m.input", 350)
            | ("4.5.1.4 (d tan)^n (a+b sec)^m.input", 413)
            | ("4.5.2.1 (a+b sec)^m (c+d sec)^n.input", 327)
            | ("4.5.7 (d trig)^m (a+b (c sec)^n)^p.input", 153)
            | ("4.5.7 (d trig)^m (a+b (c sec)^n)^p.input", 343)
            // Latest Rubi splits the sum with DownValue 2009, then terminal
            // Tangent rules {4238,4228,4238} return Unintegrable.
            | ("4.3.10 (c+d x)^m (a+b tan)^n.input", 28)
            // Latest Rubi splits these product-derivative sums with DownValue
            // 2009; terminal DownValue 7299 defers both resulting terms.
            | ("8.10 Formal derivatives.input", 29 | 48)
            // Latest Rubi normalizes the PolyLog argument with DownValue 7292,
            // then terminal DownValue 7299 defers the normalized integral.
            | ("8.8 Polylogarithm function.input", 167)
            // Latest Rubi alternates DownValues 6745 and 2005 until
            // $RecursionLimit for these positive integer quadratic powers.
            | (
                "7.4.2 Exponentials of inverse hyperbolic cotangent functions.input",
                649..=652 | 666..=669 | 685..=688 | 701..=704 | 847..=849,
            )
            // Latest Rubi starts these mixed Csch/Sech recurrences at
            // DownValue 6123 and leaves terminal DownValue 7299 integrals.
            | (
                "6.1.1 (c+d x)^m (a+b sinh)^n.input",
                591..=593 | 621..=623 | 628..=629 | 634 | 658..=660 | 665..=666 | 671,
            )
            // Latest Rubi deactivates the hyperbolic functions and applies
            // DownValue 5985, whose integration-by-parts remainder reaches
            // terminal DownValue 7299.
            | (
                "6.7.1 Hyperbolic functions.input",
                533..=535 | 549..=551 | 565..=566 | 580..=582 | 987..=989,
            )
            // Latest Rubi deactivates these Csc/Sec products and applies
            // DownValue 4920; its integration-by-parts remainders terminate
            // at DownValue 7299.
            | (
                "4.7.3 (c+d x)^m trig^n trig^p.input",
                335..=338 | 348..=350 | 354..=356,
            )
            // Latest Rubi returns deferred Int terms for these miscellaneous
            // trig cases. The traced paths terminate at DownValue 7299,
            // directly or after linearity, deactivation, or DownValue 4920.
            | (
                "4.7.7 Trig functions.input",
                1036 | 1123 | 1138..=1140 | 1180..=1181 | 1199 | 1201,
            )
            // Latest Rubi reaches terminal DownValue 7299 for these inverse
            // function compositions. The traced paths are {5276,495,684,455,
            // 223,5260,7299} for inverse-sine line 84 and direct 7299 for
            // inverse-sine line 619 and inverse-sinh line 484. The inverse-cosh
            // cases reach 7299 after DownValue 7296.
            | ("5.1.5 Inverse sine functions.input", 84 | 619)
            | ("7.1.5 Inverse hyperbolic sine functions.input", 484)
            | (
                "7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.input",
                644,
            )
            | ("7.2.5 Inverse hyperbolic cosine functions.input", 78 | 79)
            // Latest Rubi applies integration by parts and then terminal
            // DownValue 7299, leaving the resulting inner Int deferred.
            | ("7.3.4 u (a+b arctanh(c x))^p.input", 650)
            | ("7.4.1 Inverse hyperbolic cotangent functions.input", 361 | 362)
    )
}

fn with_failure_trace_note(config: &CorpusConfig, case: &Case, failure: String) -> String {
    format!("{failure}\n{}", failure_trace_note(config, case))
}

fn failure_trace_note(config: &CorpusConfig, case: &Case) -> String {
    let command = rubi_trace_command(
        case,
        config.trace_timeout_seconds,
        &config.mathematica_rubi_root,
    );
    if !config.trace_failures {
        return format!("trace with:\n{command}");
    }

    match run_rubi_failure_trace(config, case) {
        Ok(path) => format!(
            "trace command:\n{command}\ntrace saved to: {}",
            path.display()
        ),
        Err(error) => format!("trace command:\n{command}\ntrace failed: {error}"),
    }
}

fn rubi_trace_command(case: &Case, timeout_seconds: u64, rubi_root: &Path) -> String {
    format!(
        "RUBI_MATHEMATICA_RUBI_ROOT='{}' RUBI_TRACE_FILE='{}' RUBI_TRACE_LINE={} RUBI_TRACE_TIMEOUT={} /usr/local/bin/wolframscript -script scripts/trace_rubi_case.m",
        rubi_root.display(),
        case.file.display(),
        case.line,
        timeout_seconds,
    )
}

fn run_rubi_failure_trace(config: &CorpusConfig, case: &Case) -> Result<PathBuf, String> {
    fs::create_dir_all(&config.trace_output_dir).map_err(|error| {
        format!(
            "could not create trace output dir {}: {error}",
            config.trace_output_dir.display()
        )
    })?;
    let output_path = config
        .trace_output_dir
        .join(format!("{}.txt", rubi_trace_filename(case)));
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/trace_rubi_case.m");
    let output = Command::new("/usr/local/bin/wolframscript")
        .arg("-script")
        .arg(&script)
        .env("RUBI_TRACE_FILE", &case.file)
        .env(
            RUBI_MATHEMATICA_RUBI_ROOT_ENV,
            &config.mathematica_rubi_root,
        )
        .env("RUBI_TRACE_LINE", case.line.to_string())
        .env(
            "RUBI_TRACE_TIMEOUT",
            config.trace_timeout_seconds.to_string(),
        )
        .output()
        .map_err(|error| format!("could not run wolframscript: {error}"))?;

    let mut trace = Vec::new();
    trace.extend_from_slice(&output.stdout);
    if !output.stderr.is_empty() {
        trace.extend_from_slice(b"\n--- stderr ---\n");
        trace.extend_from_slice(&output.stderr);
    }
    fs::write(&output_path, trace)
        .map_err(|error| format!("could not write {}: {error}", output_path.display()))?;

    if output.status.success() {
        Ok(output_path)
    } else {
        Err(format!(
            "wolframscript exited with {}; output saved to {}",
            output.status,
            output_path.display()
        ))
    }
}

fn rubi_trace_filename(case: &Case) -> String {
    let name = format!(
        "{}_line_{}",
        case.file
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .trim_end_matches(".input"),
        case.line
    );
    name.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn panic_payload_message(payload: &(dyn Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_owned()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "<non-string panic payload>".to_owned()
    }
}

fn contains_unintegrable(expr: &Atom) -> bool {
    match expr.as_view() {
        AtomView::Fun(function) if function.get_symbol().get_stripped_name() == "unintegrable" => {
            true
        }
        AtomView::Fun(function) => function
            .into_iter()
            .any(|argument| contains_unintegrable(&argument.to_owned())),
        AtomView::Add(add) => add
            .into_iter()
            .any(|term| contains_unintegrable(&term.to_owned())),
        AtomView::Mul(mul) => mul
            .into_iter()
            .any(|factor| contains_unintegrable(&factor.to_owned())),
        AtomView::Pow(power) => {
            contains_unintegrable(&power.get_base().to_owned())
                || contains_unintegrable(&power.get_exp().to_owned())
        }
        AtomView::Num(_) | AtomView::Var(_) => false,
    }
}

fn normalize_deferred_rubi_integral_derivatives(expr: &Atom, x: Symbol) -> Atom {
    match expr.as_view() {
        AtomView::Fun(function)
            if is_symbol_named(function.get_symbol(), "der") && function.get_nargs() == 5 =>
        {
            let first_order = function.get(0).to_owned();
            let second_order = function.get(1).to_owned();
            let head = function.get(2);
            let integrand = function.get(3).to_owned();
            let variable = function.get(4).to_owned();

            if head
                .get_symbol()
                .is_some_and(|symbol| is_symbol_named(symbol, "rubi_int"))
                && variable == Atom::var(x)
            {
                if first_order == Atom::num(0) && second_order == Atom::num(1) {
                    return normalize_deferred_rubi_integral_derivatives(&integrand, x);
                }
                if first_order == Atom::num(1) && second_order == Atom::num(0) {
                    return Atom::num(0);
                }
            }

            let args: Vec<_> = function
                .into_iter()
                .map(|argument| {
                    normalize_deferred_rubi_integral_derivatives(&argument.to_owned(), x)
                })
                .collect();
            function.get_symbol().call_args(args)
        }
        AtomView::Fun(function) => {
            let args: Vec<_> = function
                .into_iter()
                .map(|argument| {
                    normalize_deferred_rubi_integral_derivatives(&argument.to_owned(), x)
                })
                .collect();
            function.get_symbol().call_args(args)
        }
        AtomView::Add(add) => add
            .into_iter()
            .map(|term| normalize_deferred_rubi_integral_derivatives(&term.to_owned(), x))
            .fold(Atom::num(0), |sum, term| sum + term),
        AtomView::Mul(mul) => mul
            .into_iter()
            .map(|factor| normalize_deferred_rubi_integral_derivatives(&factor.to_owned(), x))
            .fold(Atom::num(1), |product, factor| product * factor),
        AtomView::Pow(power) => {
            normalize_deferred_rubi_integral_derivatives(&power.get_base().to_owned(), x).pow(
                normalize_deferred_rubi_integral_derivatives(&power.get_exp().to_owned(), x),
            )
        }
        AtomView::Num(_) | AtomView::Var(_) => expr.clone(),
    }
}

fn residual_is_zero(residual: &Atom) -> bool {
    if residual.as_view().is_zero()
        || !matches!(residual.zero_test(8, 1e-10), ConditionResult::False)
        || residual_is_zero_at_complex_sample(residual)
    {
        return true;
    }

    let residual = normalize_pi_half_trig_for_verification(residual).together();
    if residual.as_view().is_zero()
        || !matches!(residual.zero_test(8, 1e-10), ConditionResult::False)
        || residual_is_zero_at_complex_sample(&residual)
    {
        return true;
    }

    let normalized = normalize_trig_radicals_for_verification(
        &normalize_pi_half_trig_for_verification(&normalize_trig_exp_for_verification(
            &normalize_atanh_for_verification(&normalize_atan_for_verification(&residual)),
        )),
    )
    .expand();
    if let Some(normalized) = cancel_for_verification(&normalized) {
        if normalized.as_view().is_zero()
            || !matches!(normalized.zero_test(8, 1e-10), ConditionResult::False)
        {
            return true;
        }
    }

    let mut symbols: Vec<_> = residual.get_all_symbols(false).into_iter().collect();
    symbols.sort();
    let parameters: Vec<_> = symbols.iter().copied().map(Atom::var).collect();
    let Ok(evaluator) = residual.evaluator(&parameters).build() else {
        return false;
    };
    let mut evaluator = evaluator.map_coeff(&|coefficient| coefficient.re.to_f64());
    let value = evaluator.evaluate_single(&vec![0.37; parameters.len()]);

    value.is_finite() && value.abs() < 1e-8
}

fn normalize_trig_radicals_for_verification(expr: &Atom) -> Atom {
    match expr.as_view() {
        AtomView::Pow(power) => {
            let base = normalize_trig_radicals_for_verification(&power.get_base().to_owned());
            let exponent = normalize_trig_radicals_for_verification(&power.get_exp().to_owned());
            if integer_ratio_for_verification(&exponent) == Some((1, 2)) {
                if let Some(rewrite) = trig_radical_rewrite_for_verification(&base) {
                    return rewrite;
                }
            }
            base.pow(exponent)
        }
        AtomView::Fun(function) => {
            let args: Vec<_> = function
                .into_iter()
                .map(|argument| normalize_trig_radicals_for_verification(&argument.to_owned()))
                .collect();
            function.get_symbol().call_args(args)
        }
        AtomView::Add(add) => add
            .into_iter()
            .map(|term| normalize_trig_radicals_for_verification(&term.to_owned()))
            .fold(Atom::num(0), |sum, term| sum + term),
        AtomView::Mul(mul) => mul
            .into_iter()
            .map(|factor| normalize_trig_radicals_for_verification(&factor.to_owned()))
            .fold(Atom::num(1), |product, factor| product * factor),
        AtomView::Num(_) | AtomView::Var(_) => expr.clone(),
    }
}

fn trig_radical_rewrite_for_verification(base: &Atom) -> Option<Atom> {
    trig_sin_cos_radical_rewrite_for_verification(base)
        .or_else(|| trig_tangent_square_denominator_radical_rewrite_for_verification(base))
}

fn trig_sin_cos_radical_rewrite_for_verification(base: &Atom) -> Option<Atom> {
    let mut sin_part = None;
    let mut cos_part = None;
    for factor in product_factors_for_verification(base) {
        if let Some((argument, exponent)) =
            trig_integer_power_for_verification(&factor, Symbol::SIN)
        {
            if sin_part.replace((argument, exponent)).is_some() {
                return None;
            }
            continue;
        }
        if let Some((argument, exponent)) =
            trig_integer_power_for_verification(&factor, Symbol::COS)
        {
            if cos_part.replace((argument, exponent)).is_some() {
                return None;
            }
            continue;
        }
        return None;
    }

    let (sin_argument, sin_exponent) = sin_part?;
    let (cos_argument, cos_exponent) = cos_part?;
    if sin_argument != cos_argument {
        return None;
    }

    let tangent = sin_argument.clone().tan();
    let secant_squared = sin_argument.sec().pow(2);
    match (sin_exponent, cos_exponent) {
        // Rubi's tangent-substitution trace treats these radicals with the
        // same branch convention as the corresponding Tan/Sec powers. This is
        // verifier-only normalization, not an integration rule.
        (1, 3) => Some(tangent.pow(Atom::num(1) / Atom::num(2)) / secant_squared),
        (3, 1) => Some(tangent.pow(Atom::num(3) / Atom::num(2)) / secant_squared),
        _ => None,
    }
}

fn trig_tangent_square_denominator_radical_rewrite_for_verification(base: &Atom) -> Option<Atom> {
    let mut tangent_part = None;
    let mut denominator_part = None;
    for factor in product_factors_for_verification(base) {
        if let Some((argument, exponent)) =
            trig_integer_power_for_verification(&factor, symbolica::transcendental::tan())
        {
            if tangent_part.replace((argument, exponent)).is_some() {
                return None;
            }
            continue;
        }
        let Some((denominator, exponent)) = reciprocal_factor_for_verification(&factor) else {
            return None;
        };
        if exponent != 1 || denominator_part.replace(denominator).is_some() {
            return None;
        }
    }

    let (argument, tangent_exponent) = tangent_part?;
    if tangent_exponent != 3 {
        return None;
    }
    let denominator = denominator_part?;
    let tangent_squared = argument.tan().pow(2);
    let expected_denominator = (Atom::num(1) + &tangent_squared).pow(2).expand();
    if denominator.expand() != expected_denominator {
        return None;
    }

    Some(argument.tan().pow(Atom::num(3) / Atom::num(2)) / (Atom::num(1) + tangent_squared))
}

fn product_factors_for_verification(expr: &Atom) -> Vec<Atom> {
    match expr.as_view() {
        AtomView::Mul(mul) => mul.into_iter().map(|factor| factor.to_owned()).collect(),
        _ => vec![expr.clone()],
    }
}

fn reciprocal_factor_for_verification(expr: &Atom) -> Option<(Atom, i64)> {
    let AtomView::Pow(power) = expr.as_view() else {
        return None;
    };
    let exponent = integer_for_verification(&power.get_exp().to_owned())?;
    (exponent < 0).then(|| (power.get_base().to_owned(), -exponent))
}

fn trig_integer_power_for_verification(expr: &Atom, symbol: Symbol) -> Option<(Atom, i64)> {
    match expr.as_view() {
        AtomView::Fun(function) if function.get_nargs() == 1 && function.get_symbol() == symbol => {
            Some((function.get(0).to_owned(), 1))
        }
        AtomView::Pow(power) => {
            let exponent = integer_for_verification(&power.get_exp().to_owned())?;
            let AtomView::Fun(function) = power.get_base() else {
                return None;
            };
            if function.get_nargs() == 1 && function.get_symbol() == symbol {
                Some((function.get(0).to_owned(), exponent))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn normalize_pi_half_trig_for_verification(expr: &Atom) -> Atom {
    match expr.as_view() {
        AtomView::Fun(function)
            if function.get_nargs() == 1 && builtin_trig_symbol_q(function.get_symbol()) =>
        {
            let argument = normalize_pi_half_trig_for_verification(&function.get(0).to_owned());
            if let Some((numerator, denominator, rest)) = pi_shift_parts_for_verification(&argument)
            {
                return reduce_trig_pi_shift_for_verification(
                    function.get_symbol(),
                    numerator,
                    denominator,
                    rest,
                );
            }
            function.get_symbol().call((argument,))
        }
        AtomView::Fun(function) => {
            let args: Vec<_> = function
                .into_iter()
                .map(|argument| normalize_pi_half_trig_for_verification(&argument.to_owned()))
                .collect();
            function.get_symbol().call_args(args)
        }
        AtomView::Add(add) => add
            .into_iter()
            .map(|term| normalize_pi_half_trig_for_verification(&term.to_owned()))
            .fold(Atom::num(0), |sum, term| sum + term),
        AtomView::Mul(mul) => mul
            .into_iter()
            .map(|factor| normalize_pi_half_trig_for_verification(&factor.to_owned()))
            .fold(Atom::num(1), |product, factor| product * factor),
        AtomView::Pow(power) => {
            normalize_pi_half_trig_for_verification(&power.get_base().to_owned()).pow(
                normalize_pi_half_trig_for_verification(&power.get_exp().to_owned()),
            )
        }
        AtomView::Num(_) | AtomView::Var(_) => expr.clone(),
    }
}

fn builtin_trig_symbol_q(symbol: Symbol) -> bool {
    symbol == Symbol::SIN
        || symbol == Symbol::COS
        || symbol == symbolica::transcendental::tan()
        || symbol == symbolica::transcendental::cot()
        || symbol == symbolica::transcendental::sec()
        || symbol == symbolica::transcendental::csc()
}

fn pi_shift_parts_for_verification(argument: &Atom) -> Option<(i64, i64, Atom)> {
    match argument.as_view() {
        AtomView::Add(add) => {
            for term in add {
                let term = term.to_owned();
                if let Some((numerator, denominator)) = pi_term_rational_for_verification(&term) {
                    return Some((numerator, denominator, (argument - &term).expand()));
                }
            }
            None
        }
        _ => pi_term_rational_for_verification(argument)
            .map(|(numerator, denominator)| (numerator, denominator, Atom::num(0))),
    }
}

fn pi_term_rational_for_verification(term: &Atom) -> Option<(i64, i64)> {
    let pi = Atom::var(Symbol::PI);
    if term == &pi {
        return Some((1, 1));
    }
    if term == &-&pi {
        return Some((-1, 1));
    }

    let coefficient = match term.as_view() {
        AtomView::Mul(mul) => {
            let mut coefficient = Atom::num(1);
            let mut found_pi = false;
            for factor in mul {
                let factor = factor.to_owned();
                if factor == pi {
                    if found_pi {
                        return None;
                    }
                    found_pi = true;
                } else if !factor.contains_symbol(Symbol::PI) {
                    coefficient *= factor;
                } else {
                    return None;
                }
            }
            found_pi.then_some(coefficient)?
        }
        _ => return None,
    };

    integer_ratio_for_verification(&coefficient)
}

fn integer_ratio_for_verification(expr: &Atom) -> Option<(i64, i64)> {
    if let Some(integer) = integer_for_verification(expr) {
        return Some((integer, 1));
    }

    let text = expr.to_string();
    if let Some((numerator, denominator)) = text.split_once('/') {
        let numerator = numerator.parse::<i64>().ok()?;
        let denominator = denominator.parse::<i64>().ok()?;
        if denominator != 0 {
            return Some((numerator, denominator));
        }
    }

    let AtomView::Mul(mul) = expr.as_view() else {
        return None;
    };
    let mut numerator = 1_i64;
    let mut denominator = 1_i64;
    for factor in mul {
        let factor = factor.to_owned();
        if let Some(integer) = integer_for_verification(&factor) {
            numerator = numerator.checked_mul(integer)?;
            continue;
        }
        let AtomView::Pow(power) = factor.as_view() else {
            return None;
        };
        if integer_for_verification(&power.get_exp().to_owned())? != -1 {
            return None;
        }
        denominator =
            denominator.checked_mul(integer_for_verification(&power.get_base().to_owned())?)?;
    }

    if denominator < 0 {
        numerator = -numerator;
        denominator = -denominator;
    }
    Some((numerator, denominator))
}

fn integer_for_verification(expr: &Atom) -> Option<i64> {
    expr.to_string().parse::<i64>().ok()
}

fn reduce_trig_pi_shift_for_verification(
    symbol: Symbol,
    numerator: i64,
    denominator: i64,
    rest: Atom,
) -> Atom {
    if numerator < 0 {
        if 4 * numerator >= -denominator {
            return symbol.call((rational_pi_argument_for_verification(
                numerator,
                denominator,
                rest,
            ),));
        }
        return match symbol {
            s if s == Symbol::SIN => {
                -reduce_trig_pi_shift_for_verification(Symbol::SIN, -numerator, denominator, -rest)
            }
            s if s == Symbol::COS => {
                reduce_trig_pi_shift_for_verification(Symbol::COS, -numerator, denominator, -rest)
            }
            s if s == symbolica::transcendental::tan() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::tan(),
                -numerator,
                denominator,
                -rest,
            ),
            s if s == symbolica::transcendental::cot() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::cot(),
                -numerator,
                denominator,
                -rest,
            ),
            s if s == symbolica::transcendental::sec() => reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::sec(),
                -numerator,
                denominator,
                -rest,
            ),
            s if s == symbolica::transcendental::csc() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::csc(),
                -numerator,
                denominator,
                -rest,
            ),
            _ => symbol.call((rational_pi_argument_for_verification(
                numerator,
                denominator,
                rest,
            ),)),
        };
    }

    if numerator >= 2 * denominator {
        return reduce_trig_pi_shift_for_verification(
            symbol,
            numerator.rem_euclid(2 * denominator),
            denominator,
            rest,
        );
    }

    if numerator >= denominator {
        return match symbol {
            s if s == Symbol::SIN => -reduce_trig_pi_shift_for_verification(
                Symbol::SIN,
                numerator - denominator,
                denominator,
                rest,
            ),
            s if s == Symbol::COS => -reduce_trig_pi_shift_for_verification(
                Symbol::COS,
                numerator - denominator,
                denominator,
                rest,
            ),
            s if s == symbolica::transcendental::tan() => reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::tan(),
                numerator - denominator,
                denominator,
                rest,
            ),
            s if s == symbolica::transcendental::cot() => reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::cot(),
                numerator - denominator,
                denominator,
                rest,
            ),
            s if s == symbolica::transcendental::sec() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::sec(),
                numerator - denominator,
                denominator,
                rest,
            ),
            s if s == symbolica::transcendental::csc() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::csc(),
                numerator - denominator,
                denominator,
                rest,
            ),
            _ => symbol.call((rational_pi_argument_for_verification(
                numerator,
                denominator,
                rest,
            ),)),
        };
    }

    if 2 * numerator >= denominator {
        return match symbol {
            s if s == Symbol::SIN => reduce_trig_pi_shift_for_verification(
                Symbol::COS,
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            s if s == Symbol::COS => -reduce_trig_pi_shift_for_verification(
                Symbol::SIN,
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            s if s == symbolica::transcendental::tan() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::cot(),
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            s if s == symbolica::transcendental::cot() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::tan(),
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            s if s == symbolica::transcendental::sec() => -reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::csc(),
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            s if s == symbolica::transcendental::csc() => reduce_trig_pi_shift_for_verification(
                symbolica::transcendental::sec(),
                2 * numerator - denominator,
                2 * denominator,
                rest,
            ),
            _ => symbol.call((rational_pi_argument_for_verification(
                numerator,
                denominator,
                rest,
            ),)),
        };
    }

    symbol.call((rational_pi_argument_for_verification(
        numerator,
        denominator,
        rest,
    ),))
}

fn rational_pi_argument_for_verification(numerator: i64, denominator: i64, rest: Atom) -> Atom {
    (Atom::num(numerator) * Atom::var(Symbol::PI) / Atom::num(denominator) + rest).expand()
}

fn residual_is_zero_at_complex_sample(residual: &Atom) -> bool {
    let mut symbols: Vec<_> = residual.get_all_symbols(false).into_iter().collect();
    symbols.sort();
    let parameters: Vec<_> = symbols.iter().copied().map(Atom::var).collect();
    let Ok(evaluator) = residual.evaluator(&parameters).build() else {
        return false;
    };
    let mut evaluator = evaluator.map_coeff(&|coefficient| coefficient.re.to_f64().into());
    let samples = [
        Complex::new(2.0, 0.3),
        Complex::new(3.0, -0.2),
        Complex::new(5.0, 0.1),
        Complex::new(0.37, 0.4),
        Complex::new(1.7, -0.5),
        Complex::new(0.8, 0.6),
    ];
    let values: Vec<_> = (0..parameters.len())
        .map(|index| samples[index % samples.len()])
        .collect();
    let value = evaluator.evaluate_single(&values);

    value.re.is_finite() && value.im.is_finite() && value.re.abs() < 1e-8 && value.im.abs() < 1e-8
}

fn cancel_for_verification(expr: &Atom) -> Option<Atom> {
    if has_inexact_float(expr.as_view()) {
        return None;
    }

    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| expr.clone().together())).ok()
}

fn rubi_special_function_heads(expr: &Atom) -> Vec<&'static str> {
    const SPECIAL_HEADS: &[&str] = &[
        "hypergeometric_2f1",
        "hypergeometric_pfq",
        "appell_f1",
        "elliptic_e",
        "elliptic_f",
        "elliptic_pi",
        "erfc",
        "erfi",
        "fresnel_s",
        "fresnel_c",
        "exp_integral_e",
        "exp_integral_ei",
        "log_integral",
        "zeta",
        "sin_integral",
        "cos_integral",
        "sinh_integral",
        "cosh_integral",
        "product_log",
        "rubi_gamma",
        "log_gamma",
        "polylog",
    ];

    fn collect(expr: AtomView<'_>, heads: &mut Vec<&'static str>) {
        match expr {
            AtomView::Fun(function) => {
                let symbol = function.get_symbol();
                let name = symbol.get_stripped_name();
                if let Some(head) = SPECIAL_HEADS.iter().copied().find(|head| *head == name)
                    && !heads.contains(&head)
                {
                    heads.push(head);
                }
                for argument in function {
                    collect(argument, heads);
                }
            }
            AtomView::Add(add) => {
                for term in add {
                    collect(term, heads);
                }
            }
            AtomView::Mul(mul) => {
                for factor in mul {
                    collect(factor, heads);
                }
            }
            AtomView::Pow(power) => {
                collect(power.get_base(), heads);
                collect(power.get_exp(), heads);
            }
            AtomView::Num(_) | AtomView::Var(_) => {}
        }
    }

    let mut heads = Vec::new();
    collect(expr.as_view(), &mut heads);
    heads
}

fn has_inexact_float(expr: AtomView<'_>) -> bool {
    match expr {
        AtomView::Num(number) => number.get_coeff_view().is_float(),
        AtomView::Var(_) => false,
        AtomView::Add(add) => add.into_iter().any(has_inexact_float),
        AtomView::Mul(mul) => mul.into_iter().any(has_inexact_float),
        AtomView::Pow(power) => {
            has_inexact_float(power.get_base()) || has_inexact_float(power.get_exp())
        }
        AtomView::Fun(function) => function.iter().any(has_inexact_float),
    }
}

fn normalize_atanh_for_verification(expr: &Atom) -> Atom {
    expr.replace_map(|part, _context, out| {
        let Some(argument) = atanh_argument(part) else {
            return;
        };

        let argument = argument.to_owned();
        **out = ((Atom::num(1) + &argument).log() - (Atom::num(1) - argument).log()) / Atom::num(2);
    })
}

fn normalize_atan_for_verification(expr: &Atom) -> Atom {
    expr.replace_map(|part, _context, out| {
        let Some(argument) = atan_argument(part) else {
            return;
        };

        let argument = argument.to_owned();
        let i = Atom::i();
        **out = &i * ((Atom::num(1) - &i * &argument).log() - (Atom::num(1) + &i * argument).log())
            / Atom::num(2);
    })
}

fn normalize_trig_exp_for_verification(expr: &Atom) -> Atom {
    match expr.as_view() {
        AtomView::Fun(function)
            if function.get_nargs() == 1
                && function.get_symbol() == symbolica::transcendental::tan() =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_2ix = corpus_e().pow(Atom::i() * Atom::num(2) * argument);
            -Atom::i() * (&exp_2ix - 1) / (exp_2ix + 1)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1
                && function.get_symbol() == symbolica::transcendental::sec() =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_ix = corpus_e().pow(Atom::i() * argument);
            Atom::num(2) * &exp_ix / (exp_ix.pow(2) + 1)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("sinh") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            (exp_pos - exp_neg) / Atom::num(2)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("cosh") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            (exp_pos + exp_neg) / Atom::num(2)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("tanh") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            (&exp_pos - &exp_neg) / (exp_pos + exp_neg)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("coth") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            (&exp_pos + &exp_neg) / (exp_pos - exp_neg)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("sech") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            Atom::num(2) / (exp_pos + exp_neg)
        }
        AtomView::Fun(function)
            if function.get_nargs() == 1 && function.get_symbol() == symbol!("csch") =>
        {
            let argument = normalize_trig_exp_for_verification(&function.get(0).to_owned());
            let exp_pos = corpus_e().pow(argument.clone());
            let exp_neg = corpus_e().pow(-argument);
            Atom::num(2) / (exp_pos - exp_neg)
        }
        AtomView::Fun(function) => {
            let args: Vec<_> = function
                .into_iter()
                .map(|argument| normalize_trig_exp_for_verification(&argument.to_owned()))
                .collect();
            function.get_symbol().call_args(args)
        }
        AtomView::Add(add) => add
            .into_iter()
            .map(|term| normalize_trig_exp_for_verification(&term.to_owned()))
            .fold(Atom::num(0), |sum, term| sum + term),
        AtomView::Mul(mul) => mul
            .into_iter()
            .map(|factor| normalize_trig_exp_for_verification(&factor.to_owned()))
            .fold(Atom::num(1), |product, factor| product * factor),
        AtomView::Pow(power) => normalize_trig_exp_for_verification(&power.get_base().to_owned())
            .pow(normalize_trig_exp_for_verification(
                &power.get_exp().to_owned(),
            )),
        AtomView::Num(_) | AtomView::Var(_) => expr.clone(),
    }
}

fn corpus_e() -> Atom {
    Atom::var(Symbol::E)
}

fn normalize_log_exp_for_verification(expr: &Atom) -> Atom {
    let normalized = expr.replace_map(|part, _context, out| {
        let Some(argument) = log_argument(part) else {
            return;
        };

        if is_e_symbol(argument) {
            **out = Atom::num(1);
            return;
        }

        if let Some(exponent) = exp_argument(argument) {
            **out = exponent.to_owned();
        }
    });

    normalized
}

fn atanh_argument(expr: AtomView<'_>) -> Option<AtomView<'_>> {
    let AtomView::Fun(function) = expr else {
        return None;
    };

    is_symbol_named(function.get_symbol(), "atanh")
        .then(|| function.get_nargs() == 1)
        .and_then(|is_unary| is_unary.then(|| function.get(0)))
}

fn atan_argument(expr: AtomView<'_>) -> Option<AtomView<'_>> {
    let AtomView::Fun(function) = expr else {
        return None;
    };

    is_symbol_named(function.get_symbol(), "atan")
        .then(|| function.get_nargs() == 1)
        .and_then(|is_unary| is_unary.then(|| function.get(0)))
}

fn log_argument(expr: AtomView<'_>) -> Option<AtomView<'_>> {
    let AtomView::Fun(function) = expr else {
        return None;
    };

    is_symbol_named(function.get_symbol(), "log")
        .then(|| function.get_nargs() == 1)
        .and_then(|is_unary| is_unary.then(|| function.get(0)))
}

fn exp_argument(expr: AtomView<'_>) -> Option<AtomView<'_>> {
    if let AtomView::Fun(function) = expr
        && is_symbol_named(function.get_symbol(), "exp")
        && function.get_nargs() == 1
    {
        return Some(function.get(0));
    }

    let AtomView::Pow(power) = expr else {
        return None;
    };
    let (base, exponent) = power.get_base_exp();
    is_e_symbol(base).then_some(exponent)
}

fn is_e_symbol(expr: AtomView<'_>) -> bool {
    expr.get_symbol().is_some_and(|symbol| symbol == Symbol::E)
}

fn is_symbol_named(symbol: Symbol, name: &str) -> bool {
    symbol.get_stripped_name() == name
}

fn parse_case_expression(case: &Case, expression: &str) -> Atom {
    let parsed = Atom::parse(
        normalize_axiom_syntax(expression),
        "rubi_corpus",
        Default::default(),
    )
    .unwrap_or_else(|error| {
        panic!(
            "{}:{}: Symbolica could not parse {expression:?}: {error}",
            case.file.file_name().unwrap_or_default().to_string_lossy(),
            case.line,
        )
    });

    normalize_corpus_function_heads(&parsed)
}

fn normalize_corpus_function_heads(expr: &Atom) -> Atom {
    match expr.as_view() {
        AtomView::Fun(function) => {
            let arguments = function
                .into_iter()
                .map(|argument| normalize_corpus_function_heads(&argument.to_owned()))
                .collect::<Vec<_>>();
            let function_symbol = function.get_symbol();
            let name = function_symbol.get_stripped_name();

            if name == "Derivative" && arguments.len() == 3 {
                return Symbol::DERIVATIVE.call((
                    arguments[0].clone(),
                    arguments[1].clone(),
                    arguments[2].clone(),
                ));
            }
            if name == "erf" && arguments.len() == 1 {
                return arguments[0].clone().erf();
            }
            if name == "Psi" && arguments.len() == 2 {
                return arguments[1].clone().polygamma(arguments[0].clone());
            }

            match (name, arguments.as_slice()) {
                ("ProductLog" | "product_log", [z]) => return z.product_log(),
                ("GAMMA" | "Gamma" | "gamma" | "rubi_gamma", [z]) => {
                    return Symbol::parse("rubi_gamma", "symbolica_integrate")
                        .expect("Rubi gamma symbol should be registered")
                        .call(z);
                }
                ("GAMMA" | "Gamma" | "gamma" | "rubi_gamma", [a, z]) => {
                    return z.rubi_gamma(a);
                }
                ("lnGAMMA" | "LogGamma" | "log_gamma", [z]) => return z.log_gamma(),
                ("Ei", [z]) | ("ExpIntegralEi" | "exp_integral_ei", [z]) => {
                    return z.exp_integral_ei();
                }
                ("Ei", [n, z]) | ("ExpIntegralE" | "exp_integral_e", [n, z]) => {
                    return z.exp_integral_e(n);
                }
                ("erfc" | "Erfc", [z]) => return z.erfc(),
                ("erfi" | "Erfi", [z]) => return z.erfi(),
                ("FresnelS" | "fresnel_s", [z]) => return z.fresnel_s(),
                ("FresnelC" | "fresnel_c", [z]) => return z.fresnel_c(),
                ("Si" | "SinIntegral" | "sin_integral", [z]) => return z.sin_integral(),
                ("Ci" | "CosIntegral" | "cos_integral", [z]) => return z.cos_integral(),
                ("Shi" | "SinhIntegral" | "sinh_integral", [z]) => {
                    return z.sinh_integral();
                }
                ("Chi" | "CoshIntegral" | "cosh_integral", [z]) => {
                    return z.cosh_integral();
                }
                ("Li" | "li" | "LogIntegral" | "log_integral", [z]) => {
                    return z.log_integral();
                }
                ("Zeta" | "zeta", [s, z]) => {
                    return symbolica::transcendental::zeta().call((s, z));
                }
                ("BesselJ" | "bessel_j", [nu, z]) => return z.bessel_j(nu),
                ("BesselY" | "bessel_y", [nu, z]) => return z.bessel_y(nu),
                ("BesselI" | "bessel_i", [nu, z]) => return z.bessel_i(nu),
                ("BesselK" | "bessel_k", [nu, z]) => return z.bessel_k(nu),
                ("Factorial", [z]) => return z.factorial(),
                _ => {}
            }

            function_symbol.call_args(arguments)
        }
        AtomView::Add(add) => add
            .into_iter()
            .map(|term| normalize_corpus_function_heads(&term.to_owned()))
            .fold(Atom::num(0), |sum, term| sum + term),
        AtomView::Mul(mul) => mul
            .into_iter()
            .map(|factor| normalize_corpus_function_heads(&factor.to_owned()))
            .fold(Atom::num(1), |product, factor| product * factor),
        AtomView::Pow(power) => normalize_corpus_function_heads(&power.get_base().to_owned())
            .pow(normalize_corpus_function_heads(&power.get_exp().to_owned())),
        AtomView::Var(variable)
            if variable.get_symbol().get_stripped_name() == "RubiEulerConstant" =>
        {
            Atom::var(Symbol::E)
        }
        AtomView::Num(_) | AtomView::Var(_) => expr.clone(),
    }
}

fn classify_expected_integral_functions(expression: &str) -> IntegralFunctionSupport {
    let mut unknown = Vec::new();
    for function in function_call_names(expression) {
        if !symbolica_knows_function(&function) && !unknown.contains(&function) {
            unknown.push(function);
        }
    }

    if unknown.is_empty() {
        IntegralFunctionSupport::Known
    } else {
        unknown.sort();
        IntegralFunctionSupport::Unknown(unknown)
    }
}

fn expected_rubi_deferred(expression: &str) -> bool {
    function_call_names(expression)
        .iter()
        .any(|function| matches!(function.as_str(), "Unintegrable" | "CannotIntegrate"))
}

fn function_call_names(expression: &str) -> Vec<String> {
    let bytes = expression.as_bytes();
    let mut names = Vec::new();
    let mut cursor = 0usize;

    while cursor < bytes.len() {
        let character = bytes[cursor] as char;
        if character.is_ascii_alphabetic() || character == '_' {
            let start = cursor;
            cursor += 1;
            while cursor < bytes.len() {
                let character = bytes[cursor] as char;
                if character.is_ascii_alphanumeric() || character == '_' {
                    cursor += 1;
                } else {
                    break;
                }
            }

            let mut lookahead = cursor;
            while lookahead < bytes.len() && (bytes[lookahead] as char).is_ascii_whitespace() {
                lookahead += 1;
            }

            if lookahead < bytes.len() && bytes[lookahead] == b'(' {
                names.push(expression[start..cursor].to_owned());
            }
        } else {
            cursor += 1;
        }
    }

    names
}

fn symbolica_knows_function(function: &str) -> bool {
    matches!(
        function,
        "abs"
            | "acos"
            | "acosh"
            | "acot"
            | "acoth"
            | "acsc"
            | "acsch"
            | "asec"
            | "asech"
            | "asin"
            | "asinh"
            | "atan"
            | "atanh"
            | "bessel_i"
            | "bessel_j"
            | "bessel_k"
            | "bessel_y"
            | "BesselI"
            | "BesselJ"
            | "BesselK"
            | "BesselY"
            | "appell_f1"
            | "conj"
            | "cos"
            | "cosh"
            | "cos_integral"
            | "cosh_integral"
            | "cot"
            | "coth"
            | "csc"
            | "csch"
            | "erf"
            | "erfc"
            | "erfi"
            | "exp_integral_e"
            | "exp_integral_ei"
            | "exp"
            | "elliptic_e"
            | "elliptic_f"
            | "elliptic_pi"
            | "fresnel_c"
            | "fresnel_s"
            | "gamma"
            | "hypergeometric_2f1"
            | "hypergeometric_pfq"
            | "log"
            | "log_gamma"
            | "log_integral"
            | "polylog"
            | "polygamma"
            | "product_log"
            | "rubi_gamma"
            | "sec"
            | "sech"
            | "sin"
            | "sin_integral"
            | "sinh"
            | "sinh_integral"
            | "sqrt"
            | "tan"
            | "tanh"
            | "zeta"
    )
}

fn normalize_axiom_syntax(expression: &str) -> String {
    normalize_square_roots(&normalize_formal_derivatives(
        &expression
            .replace("%pi", "pi")
            .replace("%e", "RubiEulerConstant")
            .replace("%i", "1i"),
    ))
}

fn normalize_formal_derivatives(expression: &str) -> String {
    let mut normalized = String::with_capacity(expression.len());
    let mut cursor = 0;

    while let Some(offset) = expression[cursor..].find("Derivative(") {
        let start = cursor + offset;
        normalized.push_str(&expression[cursor..start]);

        let order_start = start + "Derivative(".len();
        let Some(order_end) = matching_parenthesis(expression, order_start) else {
            panic!("unbalanced formal derivative order: {expression}");
        };
        let function_start = skip_ascii_whitespace(expression, order_end + 1);
        if expression.as_bytes().get(function_start) != Some(&b'(') {
            normalized.push_str("Derivative(");
            cursor = order_start;
            continue;
        }
        let Some(function_end) = matching_parenthesis(expression, function_start + 1) else {
            panic!("unbalanced formal derivative function: {expression}");
        };
        let argument_start = skip_ascii_whitespace(expression, function_end + 1);
        if expression.as_bytes().get(argument_start) != Some(&b'(') {
            normalized.push_str(&expression[start..=function_end]);
            cursor = function_end + 1;
            continue;
        }
        let Some(argument_end) = matching_parenthesis(expression, argument_start + 1) else {
            panic!("unbalanced formal derivative argument: {expression}");
        };

        normalized.push_str("Derivative(");
        normalized.push_str(&normalize_formal_derivatives(
            &expression[order_start..order_end],
        ));
        normalized.push(',');
        normalized.push_str(&normalize_formal_derivatives(
            &expression[function_start + 1..function_end],
        ));
        normalized.push(',');
        normalized.push_str(&normalize_formal_derivatives(
            &expression[argument_start + 1..argument_end],
        ));
        normalized.push(')');
        cursor = argument_end + 1;
    }

    normalized.push_str(&expression[cursor..]);
    normalized
}

fn skip_ascii_whitespace(input: &str, mut cursor: usize) -> usize {
    while input
        .as_bytes()
        .get(cursor)
        .is_some_and(u8::is_ascii_whitespace)
    {
        cursor += 1;
    }
    cursor
}

fn normalize_square_roots(expression: &str) -> String {
    let mut normalized = String::with_capacity(expression.len());
    let mut cursor = 0;

    while let Some(offset) = expression[cursor..].find("sqrt(") {
        let start = cursor + offset;
        normalized.push_str(&expression[cursor..start]);
        let argument_start = start + "sqrt(".len();
        let argument_end = matching_parenthesis(expression, argument_start)
            .unwrap_or_else(|| panic!("unbalanced sqrt expression: {expression}"));
        normalized.push('(');
        normalized.push_str(&normalize_square_roots(
            &expression[argument_start..argument_end],
        ));
        normalized.push_str(")^(1/2)");
        cursor = argument_end + 1;
    }

    normalized.push_str(&expression[cursor..]);
    normalized
}

fn matching_parenthesis(input: &str, contents_start: usize) -> Option<usize> {
    let mut depth = 1usize;
    for (offset, character) in input[contents_start..].char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(contents_start + offset);
                }
            }
            _ => {}
        }
    }
    None
}

fn input_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_input_files(root, &mut files);
    files.sort();
    files
}

fn collect_input_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", directory.display()))
    {
        let entry = entry.unwrap_or_else(|error| panic!("could not read corpus entry: {error}"));
        let path = entry.path();
        if path.is_dir() {
            collect_input_files(&path, files);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "input")
        {
            files.push(path);
        }
    }
}

fn cases_in_file(path: &Path) -> Vec<Case> {
    let contents = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", path.display()));

    contents
        .lines()
        .enumerate()
        .filter_map(|(index, line)| {
            let fields = case_fields(line)?;
            let integral_functions = classify_expected_integral_functions(fields.expected_integral);
            let expected_rubi_deferred = expected_rubi_deferred(fields.expected_integral);
            Some(Case {
                file: path.to_path_buf(),
                line: index + 1,
                integrand: fields.integrand.to_owned(),
                variable: fields.variable.to_owned(),
                integral_functions,
                expected_rubi_deferred,
            })
        })
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
struct CaseFields<'a> {
    integrand: &'a str,
    variable: &'a str,
    expected_integral: &'a str,
}

fn case_fields(line: &str) -> Option<CaseFields<'_>> {
    let line = line.trim();
    let contents = line.strip_prefix('[')?;
    let fields = top_level_fields(contents);
    if fields.len() < 4 {
        return None;
    }

    let integrand = fields[0].trim();
    let variable = fields[1].trim();
    let expected_integral = fields[3].trim();

    (!integrand.is_empty() && !variable.is_empty() && !expected_integral.is_empty()).then_some(
        CaseFields {
            integrand,
            variable,
            expected_integral,
        },
    )
}

fn top_level_fields(input: &str) -> Vec<&str> {
    let mut fields = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;

    for (index, character) in input.char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ']' if depth == 0 => {
                fields.push(input[start..index].trim());
                return fields;
            }
            ')' | ']' | '}' => {
                let Some(new_depth) = depth.checked_sub(1) else {
                    return fields;
                };
                depth = new_depth;
            }
            ',' if depth == 0 => {
                fields.push(input[start..index].trim());
                start = index + 1;
            }
            _ => {}
        }
    }

    fields
}

#[cfg(test)]
mod parser_tests {
    use super::*;

    #[test]
    fn extracts_the_top_level_case_fields() {
        assert_eq!(
            case_fields("[log(c*x^n)^(-1+q)*(a*x^m+b*log(c*x^n)^q)^p/x,x,1,result]"),
            Some(CaseFields {
                integrand: "log(c*x^n)^(-1+q)*(a*x^m+b*log(c*x^n)^q)^p/x",
                variable: "x",
                expected_integral: "result",
            }),
        );
    }

    #[test]
    fn preserves_nested_lists_when_extracting_case_fields() {
        assert_eq!(
            case_fields("[f(x),x,1,g([x, y], h(a,b)),metadata]"),
            Some(CaseFields {
                integrand: "f(x)",
                variable: "x",
                expected_integral: "g([x, y], h(a,b))",
            }),
        );
    }

    #[test]
    fn ignores_metadata_and_comments() {
        assert_eq!(case_fields("-- Integrands"), None);
        assert_eq!(case_fields("lst: '["), None);
    }

    #[test]
    fn normalizes_square_root_syntax() {
        assert_eq!(
            normalize_axiom_syntax("sqrt(1+sqrt(x))"),
            "(1+(x)^(1/2))^(1/2)"
        );
    }

    #[test]
    fn normalizes_axiom_special_function_heads_to_rubi_symbols() {
        for (input, expected) in [
            (
                "ProductLog(x)",
                parse!("symbolica_integrate::product_log(x)"),
            ),
            ("GAMMA(2,x)", parse!("symbolica_integrate::rubi_gamma(2,x)")),
            ("lnGAMMA(x)", parse!("symbolica_integrate::log_gamma(x)")),
            ("Ei(x)", parse!("symbolica_integrate::exp_integral_ei(x)")),
            (
                "Ei(1,x)",
                parse!("symbolica_integrate::exp_integral_e(1,x)"),
            ),
            ("erfc(x)", parse!("symbolica_integrate::erfc(x)")),
            ("erfi(x)", parse!("symbolica_integrate::erfi(x)")),
            ("FresnelS(x)", parse!("symbolica_integrate::fresnel_s(x)")),
            ("FresnelC(x)", parse!("symbolica_integrate::fresnel_c(x)")),
            ("Si(x)", parse!("symbolica_integrate::sin_integral(x)")),
            ("Ci(x)", parse!("symbolica_integrate::cos_integral(x)")),
            ("Shi(x)", parse!("symbolica_integrate::sinh_integral(x)")),
            ("Chi(x)", parse!("symbolica_integrate::cosh_integral(x)")),
            ("Zeta(2,x)", parse!("zeta(2,x)")),
            ("BesselJ(1,x)", parse!("bessel_j(1,x)")),
            ("BesselY(1,x)", parse!("bessel_y(1,x)")),
            ("BesselI(1,x)", parse!("bessel_i(1,x)")),
            ("BesselK(1,x)", parse!("bessel_k(1,x)")),
            ("Factorial(x)", parse!("symbolica_integrate::Factorial(x)")),
        ] {
            let parsed = Atom::parse(input, "rubi_corpus", Default::default()).unwrap();
            let normalized = normalize_corpus_function_heads(&parsed);
            assert_eq!(
                normalized, expected,
                "wrong canonical expression for {input}"
            );
        }
    }

    #[test]
    fn parses_formal_derivative_as_symbolica_derivative() {
        let normalized = normalize_axiom_syntax("Derivative(1)(f)(x)");
        let parsed = Atom::parse(normalized, "rubi_corpus", Default::default()).unwrap();
        let parsed = normalize_corpus_function_heads(&parsed);
        let expected = Symbol::DERIVATIVE.call((
            Atom::num(1),
            Atom::var(Symbol::parse("f", "rubi_corpus").unwrap()),
            Atom::var(Symbol::parse("x", "rubi_corpus").unwrap()),
        ));

        assert_eq!(parsed, expected, "parsed formal derivative: {parsed}");
    }

    #[test]
    fn normalizes_axiom_psi_to_symbolica_polygamma() {
        let parsed = Atom::parse("Psi(2,x)", "rubi_corpus", Default::default()).unwrap();
        let normalized = normalize_corpus_function_heads(&parsed);
        let AtomView::Fun(function) = normalized.as_view() else {
            panic!("Psi should become polygamma");
        };
        assert_eq!(function.get_symbol().get_stripped_name(), "polygamma");
    }

    #[test]
    fn normalizes_log_exp_identities_for_verification() {
        assert_eq!(
            normalize_log_exp_for_verification(&parse!("log(exp(cos(x)))")),
            parse!("cos(x)")
        );

        let x = Symbol::parse("x", "rubi_corpus").unwrap();
        let namespaced = Atom::var(Symbol::E).pow(Atom::var(x).cos()).log();
        assert_eq!(
            normalize_log_exp_for_verification(&namespaced),
            Atom::parse("cos(x)", "rubi_corpus", Default::default()).unwrap(),
        );

        let namespaced_e = Atom::var(Symbol::E).log();
        assert_eq!(
            normalize_log_exp_for_verification(&namespaced_e),
            Atom::num(1),
        );
    }

    #[test]
    fn normalizes_atan_log_identity_for_verification() {
        let x = symbol!("x");
        let x_atom = Atom::var(x);
        let i = Atom::i();
        let residual = Atom::num(1) / 2
            * (-Atom::num(2) * x_atom.atan() - &i * (Atom::num(1) + &i * &x_atom).log()
                + &i * (Atom::num(1) - &i * &x_atom).log())
            * x_atom.log()
            / x_atom;

        assert!(residual_is_zero(&residual));
    }

    #[test]
    fn normalizes_trig_exp_identity_for_verification() {
        let x = symbol!("x");
        let x_atom = Atom::var(x);
        let i = Atom::i();
        let exp_2ix = Atom::var(Symbol::E).pow(Atom::num(2) * &i * &x_atom);
        let sec_squared = x_atom.sec().pow(2);
        let tan_squared = x_atom.tan().pow(2);
        let residual = Atom::num(1) / 2
            * &x_atom
            * (-Atom::num(3) * &sec_squared
                - Atom::num(4) * &exp_2ix
                - Atom::num(16) * &exp_2ix * tan_squared
                + Atom::num(10) * &exp_2ix * &sec_squared
                - Atom::num(3) * exp_2ix.pow(2) * sec_squared)
            / ((-&i / 2 + x_atom.tan())
                * (&i / 2 + x_atom.tan())
                * (-Atom::num(3) + Atom::num(10) * &exp_2ix - Atom::num(3) * exp_2ix.pow(2)));

        assert!(residual_is_zero(&residual));
    }

    #[test]
    fn normalizes_tangent_substitution_radicals_for_verification() {
        assert_eq!(
            normalize_trig_radicals_for_verification(&parse!("(sin(x)*cos(x)^3)^(1/2)")),
            parse!("tan(x)^(1/2)/sec(x)^2")
        );
        assert_eq!(
            normalize_trig_radicals_for_verification(&parse!("(sin(x)^3*cos(x))^(1/2)")),
            parse!("tan(x)^(3/2)/sec(x)^2")
        );
        assert_eq!(
            normalize_trig_radicals_for_verification(&parse!(
                "(tan(x)^3/(1+2*tan(x)^2+tan(x)^4))^(1/2)"
            )),
            parse!("tan(x)^(3/2)/(1+tan(x)^2)")
        );
    }

    #[test]
    fn classifies_expected_integrals_with_only_symbolica_functions_as_known() {
        assert_eq!(
            classify_expected_integral_functions("atan(x)+polylog(2,x)+sqrt(x)"),
            IntegralFunctionSupport::Known,
        );
    }

    #[test]
    fn classifies_expected_integrals_with_new_functions_as_unknown() {
        assert_eq!(
            classify_expected_integral_functions("elliptic_f(x,2)+Ei(x)+CannotIntegrate(x,x)"),
            IntegralFunctionSupport::Unknown(vec!["CannotIntegrate".to_owned(), "Ei".to_owned(),]),
        );
    }
}
