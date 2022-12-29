#! /opt/homebrew/bin/fish

count (git status --porcelain) > /dev/null; and echo "Git index must be empty"; and exit 1

set releaseTag (grep "^version" crates/sylver-cli/Cargo.toml | grep -Eo "[0-9]+\.[0-9]+\.[0-9]+")

git tag v$releaseTag; and git push origin --tags; and echo "release v$releaseTag on the way !"
