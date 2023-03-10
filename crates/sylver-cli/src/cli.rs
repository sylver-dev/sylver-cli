use std::path::PathBuf;

use clap::{ArgGroup, Parser, Subcommand};

use sylver_core::specs::stem::project::ProjectLang;

#[derive(Parser, Debug)]
#[clap(version)]
/// Sylver is a language-agnostic source code analyzer.
/// Find out more at https://docs.sylver.dev/docs/getting_started
pub struct Cli {
    #[clap(subcommand)]
    pub command: Commands,

    /// Disable colored output.
    #[clap(long)]
    pub no_color: bool,

    /// Override server URL.
    #[clap(long, default_value_t = String::from("https://api.sylver.dev"))]
    pub server_url: String,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Automatically detect projects and install the appropriate rulesets.
    Init(InitCmd),
    /// Run all of the configured rulesets.
    Check(CheckCmd),
    /// Parse a single file.
    Parse(ParseCmd),
    /// Start a repl session, or run a given query against a set of files.
    Query(QueryCmd),
    /// Install and run rulesets.
    Ruleset(RulesetCmd),
}

#[derive(Parser, Debug)]
pub struct InitCmd {
    /// Override the default configuration path
    #[clap(long, default_value_t = String::from("sylver.yaml"))]
    pub config_path: String,
}

#[derive(Parser, Debug)]
#[command(group(ArgGroup::new("api_upload").requires_all(["upload", "token"])))]
pub struct CheckCmd {
    /// Override the default config file location
    #[clap(short, long, value_parser)]
    pub config: Option<PathBuf>,

    /// Upload this results of the analysis to the Cloud Dashboard
    #[clap(long)]
    pub upload: bool,

    #[clap(long, default_value_t = String::from("https://api.sylver.dev"))]
    pub upload_url: String,

    /// API token for the current repository
    #[clap(long)]
    pub token: Option<String>,
}

#[derive(Parser, Debug)]
pub struct ParseCmd {
    /// Path to the language spec.
    #[clap(short, long, value_parser)]
    pub spec: PathBuf,

    /// Path of the file to parse.
    #[clap(short, long, value_parser)]
    pub file: PathBuf,

    /// Override the default starting rule.
    #[clap(short, long)]
    pub rule: Option<String>,
}

#[derive(Parser, Debug)]
pub struct QueryCmd {
    /// Path to the language spec.
    #[clap(short, long, value_parser)]
    pub language: ProjectLang,

    /// Glob patterns of the files to include.
    #[clap(short, long, num_args = 1.., required = true)]
    pub files: Vec<String>,

    /// Glob patterns of the files to exlude
    #[clap(long, num_args = 1..)]
    pub exclude: Vec<String>,

    /// Query to execute.
    #[clap(short, long)]
    pub query: Option<String>,
}

#[derive(Parser, Debug)]
pub struct RulesetCmd {
    #[clap(subcommand)]
    pub command: RulesetCmds,
}

#[derive(Subcommand, Debug)]
pub enum RulesetCmds {
    /// Run one or more rulesets against a set of files
    Run(RulesetRun),
}

#[derive(Parser, Debug)]
pub struct RulesetRun {
    /// Paths to the rulesets to run.
    #[clap(short, long, value_parser, required = true)]
    pub rulesets: Vec<String>,

    /// Glob patterns of the files to include.
    #[clap(short, long, required = true)]
    pub files: Vec<String>,

    /// Glob patterns of the files to exlude
    #[clap(long, num_args = 1..)]
    pub exclude: Vec<String>,
}
