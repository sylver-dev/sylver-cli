use std::path::PathBuf;

use assert_cmd::Command;
use temp_dir::TempDir;

static JSON_SPEC: &str = include_str!("../test_res/json_variables/json.syl");
static VARIABLES_RULESET: &str = include_str!("../test_res/json_variables/ruleset.yaml");
static VARIABLES_VALID: &str = include_str!("../test_res/json_variables/valid_config.json");
static VARIABLES_INVALID: &str = include_str!("../test_res/json_variables/invalid_config.json");
static VARIABLES_PROJECT: &str = include_str!("../test_res/json_variables/sylver.yaml");

#[test]
fn fail_if_no_config() {
    let dir = TempDir::new().unwrap();

    Command::cargo_bin("sylver")
        .unwrap()
        .current_dir(dir.path())
        .arg("check")
        .assert()
        .failure();
}

#[test]
fn check_without_violations() {
    let dir = TempDir::new().unwrap();

    create_tmp_child(&dir, "sylver.yaml", VARIABLES_PROJECT).unwrap();
    create_tmp_child(&dir, "ruleset.yaml", VARIABLES_RULESET).unwrap();
    create_tmp_child(&dir, "json.syl", JSON_SPEC).unwrap();
    create_tmp_child(&dir, "config.json", VARIABLES_VALID).unwrap();

    Command::cargo_bin("sylver")
        .unwrap()
        .current_dir(dir.path())
        .arg("check")
        .assert()
        .success()
        .stdout("");
}

#[test]
fn check_with_violations_fails() {
    let dir = TempDir::new().unwrap();

    create_tmp_child(&dir, "sylver.yaml", VARIABLES_PROJECT).unwrap();
    create_tmp_child(&dir, "ruleset.yaml", VARIABLES_RULESET).unwrap();
    create_tmp_child(&dir, "json.syl", JSON_SPEC).unwrap();
    create_tmp_child(&dir, "config.json", VARIABLES_VALID).unwrap();
    create_tmp_child(&dir, "invalid_config.json", VARIABLES_INVALID).unwrap();

    let expected_output = include_str!("../test_res/outputs/check/invalid_config_output");

    Command::cargo_bin("sylver")
        .unwrap()
        .current_dir(dir.path())
        .arg("--no-color")
        .arg("check")
        .assert()
        .failure()
        .stdout(expected_output);
}

#[test]
fn check_min_level() {
    let dir = TempDir::new().unwrap();

    create_tmp_child(&dir, "sylver.yaml", VARIABLES_PROJECT).unwrap();
    create_tmp_child(&dir, "ruleset.yaml", VARIABLES_RULESET).unwrap();
    create_tmp_child(&dir, "json.syl", JSON_SPEC).unwrap();
    create_tmp_child(&dir, "invalid_config.json", VARIABLES_INVALID).unwrap();

    let expected_output =
        include_str!("../test_res/outputs/check/invalid_config_output_min_level_error");

    Command::cargo_bin("sylver")
        .unwrap()
        .current_dir(dir.path())
        .arg("--no-color")
        .arg("check")
        .arg("--min-level=error")
        .assert()
        .failure()
        .stdout(expected_output);
}

pub fn create_tmp_child(dir: &TempDir, name: &str, content: &str) -> std::io::Result<PathBuf> {
    let path = dir.child(name);
    std::fs::write(&path, content)?;
    Ok(path)
}
