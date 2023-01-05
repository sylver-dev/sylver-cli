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
curl -s https://www.sylver.dev/install.sh | bash
```

## From source
Sylver is written in Rust, so you need to have the Rust toolchain installed. You can install it from [rustup](https://rustup.rs/). 
To build sylver:
```
git clone https://github.com/sylver-dev/sylver-cli.git
cd sylver-cli 
cargo build --release
```

# Example

**Sylver** helps you build your linters instead of starting from scratch.
* Tutorial for a Javascript linter: [blog.sylver.dev](https://blog.sylver.dev/build-a-custom-javascript-linter-in-5-minutes)
* Tutorial for a Go linter: [blog.sylver.dev](https://blog.sylver.dev/build-a-custom-go-linter-in-5-minutes)
* Tutorial for a JSON validator: [blog.sylver.dev](https://blog.sylver.dev/building-a-json-validator-with-sylver-part13-writing-a-json-parser-in-49-lines-of-code)
