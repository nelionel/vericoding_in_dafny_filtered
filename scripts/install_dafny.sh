#!/usr/bin/env bash
set -euo pipefail

# Repo-friendly Dafny installer (persistent installation)
# - Installs wherever you choose (defaults inside this repo)
# - Uses Dafny's bundled .NET runtime (no separate .NET SDK installation)
# - Writes an env file you can source; optionally adds it to ~/.bashrc
# - Verifies installation by running a hello world and verification test

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEFAULT_INSTALL_ROOT="$REPO_ROOT/.local/dafny"
DEFAULT_ENV_FILE="$REPO_ROOT/.dafny_env"
INSTALL_ROOT=""
ENV_FILE=""
AUTO_YES=0

log() {
  echo "[${0##*/}] $(date -Iseconds) - $*"
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    log "Missing required command: $1"
    exit 1
  fi
}

ensure_root_pkgs() {
  if [ "${EUID:-$(id -u)}" -ne 0 ]; then
    if command -v sudo >/dev/null 2>&1; then
      sudo "$@"
    else
      log "This step requires root. Please install sudo or re-run this script as root."
      exit 1
    fi
  else
    "$@"
  fi
}

check_existing_installation() {
  if [ -d "$INSTALL_ROOT" ] && [ -f "$ENV_FILE" ]; then
    log "Dafny already installed at $INSTALL_ROOT"

    if grep -q "source $ENV_FILE" ~/.bashrc 2>/dev/null || grep -q ". $ENV_FILE" ~/.bashrc 2>/dev/null; then
      log "Already configured in ~/.bashrc"
    else
      log "Adding to ~/.bashrc for automatic loading"
      setup_shell_integration
    fi

    # shellcheck disable=SC1090
    source "$ENV_FILE"

    log "Verifying existing installation..."
    if command -v dafny >/dev/null 2>&1; then
      dafny --version
      log "Existing Dafny installation is functional. Skipping installation."
      log ""
      log "To use in new terminals, run: source $ENV_FILE"
      log "Or it will auto-load from ~/.bashrc in new bash sessions"
      return 0
    else
      log "Existing installation found but not functional. Reinstalling..."
      return 1
    fi
  fi
  return 1
}

prompt_install_root() {
  if [ -n "$INSTALL_ROOT" ]; then
    return
  fi
  if [ "$AUTO_YES" -eq 1 ]; then
    INSTALL_ROOT="$DEFAULT_INSTALL_ROOT"
    return
  fi
  read -r -p "Enter Dafny installation directory [$DEFAULT_INSTALL_ROOT]: " response
  if [ -z "$response" ]; then
    INSTALL_ROOT="$DEFAULT_INSTALL_ROOT"
  else
    INSTALL_ROOT="$response"
  fi
}

setup_shell_integration() {
  log "Setting up shell integration referencing $ENV_FILE"

  if [ -f ~/.bashrc ]; then
    if ! grep -q "source $ENV_FILE" ~/.bashrc 2>/dev/null && ! grep -q ". $ENV_FILE" ~/.bashrc 2>/dev/null; then
      cat >> ~/.bashrc << EOF

# Dafny environment (vericoding clean evals)
if [ -f "$ENV_FILE" ]; then
  source "$ENV_FILE"
fi
EOF
      log "Added Dafny environment to ~/.bashrc"
    fi
  fi

  if [ -f ~/.bash_profile ]; then
    if ! grep -q "source $ENV_FILE" ~/.bash_profile 2>/dev/null && ! grep -q ". $ENV_FILE" ~/.bash_profile 2>/dev/null; then
      cat >> ~/.bash_profile << EOF

# Dafny environment (vericoding clean evals)
if [ -f "$ENV_FILE" ]; then
  source "$ENV_FILE"
fi
EOF
      log "Added Dafny environment to ~/.bash_profile"
    fi
  fi
}

parse_args() {
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --install-root|-d)
        INSTALL_ROOT="$2"
        shift 2
        ;;
      --env-file)
        ENV_FILE="$2"
        shift 2
        ;;
      -y|--yes)
        AUTO_YES=1
        shift
        ;;
      -h|--help)
        cat <<EOF
Usage: $(basename "$0") [options]

Options:
  --install-root <dir>   Directory to install Dafny into (default: $DEFAULT_INSTALL_ROOT)
  --env-file <file>      Path to the env file to create (default: $DEFAULT_ENV_FILE)
  -y, --yes              Non-interactive mode
  -h, --help             Show this help message
EOF
        exit 0
        ;;
      *)
        echo "Unknown argument: $1"
        exit 1
        ;;
    esac
  done
}

normalize_path() {
  python3 - "$1" <<'PY'
import os, sys
print(os.path.abspath(os.path.expanduser(sys.argv[1])))
PY
}

main() {
  parse_args "$@"
  prompt_install_root

  INSTALL_ROOT="$(normalize_path "$INSTALL_ROOT")"
  if [ -z "$ENV_FILE" ]; then
    ENV_FILE="$DEFAULT_ENV_FILE"
  fi
  ENV_FILE="$(normalize_path "$ENV_FILE")"

  log "Installing Dafny to $INSTALL_ROOT"
  log "Environment file: $ENV_FILE"

  if command -v dafny >/dev/null 2>&1; then
    existing_bin="$(command -v dafny)"
    log "Detected Dafny on PATH ($existing_bin)."
    if [ "$AUTO_YES" -eq 0 ]; then
      read -r -p "Continue with new installation? [y/N]: " response
      case "$response" in
        [yY][eE][sS]|[yY]) ;;
        *) log "Cancelling install."; exit 0 ;;
      esac
    fi
  fi

  if check_existing_installation; then
    exit 0
  fi

  if [ ! -r /etc/os-release ]; then
    log "/etc/os-release not found. This script targets Ubuntu-based systems."
    exit 1
  fi

  # shellcheck disable=SC1091
  . /etc/os-release

  log "Installing prerequisites (curl, unzip, ca-certificates, jq)"
  ensure_root_pkgs apt-get update -y
  ensure_root_pkgs apt-get install -y curl unzip ca-certificates jq
  ensure_root_pkgs update-ca-certificates || true

  require_cmd curl
  require_cmd jq
  require_cmd unzip

  version_id="${VERSION_ID:-22.04}"
  latest_api="https://api.github.com/repos/dafny-lang/dafny/releases/latest"

  log "Fetching latest Dafny release asset list"
  urls=$(curl -fsSL "$latest_api" | jq -r '.assets[].browser_download_url')

  url=$(echo "$urls" | grep -E "x64-ubuntu-${version_id//./\\.}\\.zip$" | head -n1 || true)
  if [ -z "${url}" ]; then
    url=$(echo "$urls" | grep -E 'x64-ubuntu-(24|22|20)\.04\.zip$' | head -n1 || true)
  fi

  if [ -z "${url}" ]; then
    log "Could not find a suitable Dafny Linux ZIP asset in the latest release."
    exit 1
  fi

  log "Selected Dafny asset: $url"

  work_zip="/tmp/dafny.zip"
  log "Downloading Dafny to $work_zip"
  curl -fL "$url" -o "$work_zip"

  if [ -d "$INSTALL_ROOT" ]; then
    ts=$(date +%s)
    log "Existing $INSTALL_ROOT detected; backing up to ${INSTALL_ROOT}.bak.$ts"
    mv "$INSTALL_ROOT" "${INSTALL_ROOT}.bak.$ts"
  fi

  mkdir -p "$INSTALL_ROOT"

  log "Unzipping Dafny into $INSTALL_ROOT"
  unzip -q "$work_zip" -d "$INSTALL_ROOT"
  rm -f "$work_zip"

  candidate=$(find "$INSTALL_ROOT" -maxdepth 3 -type f -name dafny | head -n1 || true)

  if [ -z "${candidate}" ]; then
    log "Failed to locate 'dafny' executable under $INSTALL_ROOT"
    exit 1
  fi

  chmod +x "$candidate" || true
  bin_dir=$(dirname "$candidate")
  log "Using Dafny bin_dir: $bin_dir"

  mkdir -p "$(dirname "$ENV_FILE")"
  log "Creating environment file at $ENV_FILE"
  cat > "$ENV_FILE" << EOF
# Dafny environment (generated by scripts/install_dafny.sh)
# Source this to add Dafny to your PATH

export DAFNY_HOME="$(printf '%s' "$INSTALL_ROOT")"
export PATH="\$DAFNY_HOME/dafny:\$PATH"
EOF

  chmod 0644 "$ENV_FILE"

  # shellcheck disable=SC1090
  source "$ENV_FILE"

  setup_shell_integration

  log "Verifying Dafny installation"
  command -v dafny >/dev/null 2>&1 || { log "dafny not found on PATH after install"; exit 1; }
  dafny --version

  cat > /tmp/dafny_hello.dfy << 'EOF'
method Main() {
  print "Hello, Dafny!\n";
}
EOF
  dafny /tmp/dafny_hello.dfy >/dev/null
  rm -f /tmp/dafny_hello.dfy

  cat > /tmp/dafny_sum.dfy << 'EOF'
method Sum(n: nat) returns (s: nat)
  ensures s == n * (n + 1) / 2
{
  var i := 0;
  s := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant s == i * (i - 1) / 2
  {
    s := s + i;
    i := i + 1;
  }
}
EOF
  dafny /tmp/dafny_sum.dfy >/dev/null
  rm -f /tmp/dafny_sum.dfy

  log "Dafny installation complete!"
  log ""
  log "To use Dafny in this session, run: source $ENV_FILE"
  log "New shells will auto-load it via ~/.bashrc / ~/.bash_profile"
}

main "$@"

