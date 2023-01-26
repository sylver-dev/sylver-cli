<p align="center">
    <a href="https://sylver.dev"><img src="https://raw.githubusercontent.com/sylver-dev/sylver-cli/master/logo.png" height="100" alt="Sylver logo"/></a>
</p>
<h3 align="center">
  Language agnostic source code exploration and analysis.
</h3>

<div align="center" style="font-weight: bolder">
    <a href="https://app.sylver.dev">Dashboard</a> |
    <a href="https://discord.gg/PaVTgTSSxu">Discord</a> | 
    <a href="https://blog.sylver.dev">Blog</a> | 
    <a href="https://twitter.com/Geoffrey198">Twitter</a>
</div>

# Installation

## Binary releases

```
curl -s https://sylver.dev/install.sh | bash
```

## From source
Sylver is written in Rust, so you need to have the Rust toolchain installed. You can install it from [rustup](https://rustup.rs/). 
To build sylver:
```
git clone https://github.com/sylver-dev/sylver-cli.git
cd sylver-cli 
cargo build --release
```

# Running your first analysis

The following command will automatically detect the language(s) of your project and install the corresponding rulesets
from the registry:
```bash
sylver init
```

You can then run the analysis:
```bash
sylver check
```

The source of the rulesets is available at [https://github.com/sylver-dev/rulesets](https://github.com/sylver-dev/rulesets).

# Writing your own rulesets

* Tutorial for a Python: [blog.sylver.dev](https://blog.sylver.dev/build-a-custom-python-linter-in-5-minutes)
* Tutorial for a Javascript: [blog.sylver.dev](https://blog.sylver.dev/build-a-custom-javascript-linter-in-5-minutes)
* Tutorial for a Go linter: [blog.sylver.dev](https://blog.sylver.dev/build-a-custom-go-linter-in-5-minutes)
* Tutorial for a JSON: [blog.sylver.dev](https://blog.sylver.dev/building-a-json-validator-with-sylver-part13-writing-a-json-parser-in-49-lines-of-code)
