#!/usr/bin/env bash
set -euo pipefail

if [[ ${OS:-} = Windows_NT ]]; then
    echo 'error: Cannot use the install script on this platform, you can download the binary at \
    https://github.com/geoffreycopin/sylver-distrib/releases/latest'
    exit 1
fi

# Reset
Color_Off=''

# Regular Colors
Red=''
Green=''
Dim='' # White

# Bold
Bold_White=''
Bold_Green=''

if [[ -t 1 ]]; then
    # Reset
    Color_Off='\033[0m' # Text Reset

    # Regular Colors
    Red='\033[0;31m'   # Red
    Green='\033[0;32m' # Green
    Dim='\033[0;2m'    # White

    # Bold
    Bold_Green='\033[1;32m' # Bold Green
    Bold_White='\033[1m'    # Bold White
fi

error() {
    echo -e "${Red}error${Color_Off}:" "$@" >&2
    exit 1
}

info() {
    echo -e "${Dim}$@ ${Color_Off}"
}

info_bold() {
    echo -e "${Bold_White}$@ ${Color_Off}"
}

success() {
    echo -e "${Green}$@ ${Color_Off}"
}

GITHUB=${GITHUB-"https://github.com"}
GITHUB_API=${GITHUB_API-"https://api.github.com"}

repo="geoffreycopin/sylver-distrib"
github_repo="$GITHUB/$repo"

LATEST_VERSION=$(curl -s $GITHUB_API/repos/$repo/releases/latest | grep "\"tag_name\":" | grep -Eo "[0-9]+\.[0-9]+\.[0-9]+")

CURRENT_VERSION=$((command -v sylver &> /dev/null && sylver --version | grep -Eo "[0-9]+\.[0-9]+\.[0-9]+") || echo "")

if [[ $CURRENT_VERSION == $LATEST_VERSION ]]
then
  info_bold "sylver is already up-to-date"
  exit 0
elif [[ $CURRENT_VERSION ]]
then
  info "sylver $CURRENT_VERSION is already installed, updating to version $LATEST_VERSION..."
else
  info "Installing sylver $LATEST_VERSION"
fi

case $(uname -ms) in
'Darwin x86_64')
    target=x86_64-macos
    ;;
'Darwin arm64')
    target=aarch64-macos
    ;;
'Linux aarch64' | 'Linux arm64')
    target=aarch64-linux
    ;;
'Linux x86_64' | *)
    target=x86_64-linux
    ;;
esac

if [[ $target = x86_64-macos ]]; then
    # Is this process running in Rosetta?
    # redirect stderr to devnull to avoid error message when not running in Rosetta
    if [[ $(sysctl -n sysctl.proc_translated 2>/dev/null) = 1 ]]; then
        target=aarch64-macos
        info "Your shell is running in Rosetta 2. Downloading bun for $target instead"
    fi
fi

download_directory="sylver--$target"
download_archive="$download_directory.tar.xz"

sylver_uri=$github_repo/releases/latest/download/$download_archive

install_env=SYLVER_INSTALL
bin_env=\$$install_env/bin

install_dir=${!install_env:-$HOME/.sylver}
bin_dir=$install_dir/bin
exe=$bin_dir/sylver

if [[ ! -d $bin_dir ]]; then
    mkdir -p "$bin_dir" ||
        error "Failed to create install directory \"$bin_dir\""
fi

curl --fail --location --progress-bar --output $download_archive "$sylver_uri" ||
  error "Could not download sylver from $sylver_uri"

mkdir $download_directory ||
  echo "Failed to create the extraction directory"

tar -xf $download_archive --directory $download_directory||
  error "Failed to extract sylver"

mv "$download_directory/sylver" $exe ||
  error "Failed to move extracted sylver to destination"

chmod +x $exe ||
  error "Failed to set the permissions on sylver executable"

rm -r $download_archive $download_directory

tildify() {
    if [[ $1 = $HOME/* ]]; then
        local replacement=\~/

        echo "${1/$HOME\//$replacement}"
    else
        echo "$1"
    fi
}

success "sylver was successfully installed to $Bold_Green $(tildify "$exe")"
echo

refresh_command=''

tilde_install_dir=$(tildify "$bin_dir")

case $(basename "$SHELL") in
fish)
    command="fish_add_path -g $tilde_install_dir"

    fish_config=$HOME/.config/fish/config.fish
    tilde_fish_config=$(tildify "$fish_config")

    if [[ -w $fish_config ]]; then
      {
          echo -e '\n# sylver'
          echo "$command"
      } >>"$fish_config"

      info "Added \"$tilde_install_dir\" to \$PATH in \"$tilde_fish_config\""

      refresh_command="source $tilde_fish_config"
    else
      echo "Please add the install dir to $tilde_fish_config (or similar):"
      info_bold "$command"
    fi
;;

zsh)
  command="export PATH=$tilde_install_dir:\$PATH"

  zsh_config=$HOME/.zshrc
  tilde_zsh_config=$(tildify "$zsh_config")

  if [[ -w $zsh_config ]]; then
      {
          echo -e '\n# bun'
          echo "$command"
      } >>"$zsh_config"

      info "Added \"$tilde_install_dir\" to \$PATH in \"$tilde_zsh_config\""

      refresh_command="exec $SHELL"
  else
      echo "Manually add the directory to $tilde_zsh_config (or similar):"
      info_bold "$command"
  fi
;;

bash)
  command="export PATH=$tilde_install_dir:\$PATH"

  bash_configs=(
    "$HOME/.bashrc"
    "$HOME/.bash_profile"
  )

  if [[ ${XDG_CONFIG_HOME:-} ]]; then
    bash_configs+=(
        "$XDG_CONFIG_HOME/.bash_profile"
        "$XDG_CONFIG_HOME/.bashrc"
        "$XDG_CONFIG_HOME/bash_profile"
        "$XDG_CONFIG_HOME/bashrc"
    )
  fi

  set_manually=true
  for bash_config in "${bash_configs[@]}"; do
      tilde_bash_config=$(tildify "$bash_config")

      if [[ -w $bash_config ]]; then
          {
              echo -e '\n# bun'
              echo "$command"
          } >>"$bash_config"

          info "Added \"$tilde_install_dir\" to \$PATH in \"$tilde_bash_config\""

          refresh_command="source $bash_config"
          set_manually=false
          break
      fi
  done

  if [[ $set_manually = true ]]; then
      echo "Manually add the directory to $tilde_install_dir (or similar):"
      info_bold "$command"
  fi
;;

*)
  echo "Manually add $tilde_install_dir to your path:"
  info_bold "export PATH=\"$tilde_install_dir\":\$PATH"
;;
esac

echo
info "To get started, run:"
echo

if [[ $refresh_command ]]; then
    info_bold "$refresh_command"
fi

info_bold "sylver --help"

