<p align="center">
    <a href="https://sylver.dev"><img src="https://raw.githubusercontent.com/sylver-dev/sylver-cli/master/logo.png" height="100" alt="Sylver logo"/></a>
</p>
<h3 align="center">
  Language agnostic source code exploration and analysis.
</h3>

# Instalation

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