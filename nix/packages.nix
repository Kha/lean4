{ pkgs, nix, ... } @ args:
with pkgs;
let
  nix-pinned = writeShellScriptBin "nix" ''
    ${nix.packages.${system}.default}/bin/nix --experimental-features 'nix-command flakes' --extra-substituters https://lean4.cachix.org/ --option warn-dirty false "$@"
  '';
  # https://github.com/NixOS/nixpkgs/issues/130963
  lean-llvm =
    let bin = fetchTarball {
      url = "https://github.com/leanprover/lean-llvm/releases/download/15.0.1/lean-llvm-x86_64-linux-gnu.tar.zst";
      sha256 = "06j8g3ykzl49idgcd32w1f80ys9xj50a2k5vxh5qvnfk8faf4xwj";
        };
    in runCommand "lean-llvm" { buildInputs = [ makeWrapper ]; } ''
      mkdir -p $out/{bin,lib}
      (cd ${bin}; cp --parents bin/{clang,ld.lld,llvm-ar,llvm-config} lib/lib{clang-cpp,LLVM}*.so* $out)
      cp ${bin}/lib/*/lib{c++,c++abi,unwind}.* ${zlib}/lib/libz.so* ${gmp}/lib/libgmp.so* ${gcc.cc.lib}/lib/libatomic.so* $out/lib/
      cd $out/bin
      chmod u+w *
      #mv clang .clang-unwrapped
      wrapProgram $out/bin/clang
      sed -i "s!\"\$0\"!\\0 $(< ${bintools}/nix-support/dynamic-linker) --argv0 \\0!" clang
      #patchelf --set-interpreter $(< ${bintools}/nix-support/dynamic-linker) $out/bin/*
      ln -s clang cc
      ln -s clang c++
    '' // { lib = ""; };
  cc = (ccacheWrapper.override rec {
    cc = wrapCC lean-llvm;
    extraConfig = ''
      export CCACHE_DIR=/nix/var/cache/ccache
      export CCACHE_UMASK=007
      export CCACHE_BASE_DIR=$NIX_BUILD_TOP
      # https://github.com/NixOS/nixpkgs/issues/109033
      args=("$@")
      for ((i=0; i<"''${#args[@]}"; i++)); do
        case ''${args[i]} in
          -frandom-seed=*) unset args[i]; break;;
        esac
      done
      set -- "''${args[@]}"
      [ -d $CCACHE_DIR ] || exec ${cc}/bin/$(basename "$0") "$@"
    '';
  }).overrideAttrs (old: {
    # https://github.com/NixOS/nixpkgs/issues/119779
    installPhase = builtins.replaceStrings ["use_response_file_by_default=1"] ["use_response_file_by_default=0"] old.installPhase;
  });
  lean = callPackage (import ./bootstrap.nix) (args // {
    stdenv = overrideCC stdenv cc;
    inherit buildLeanPackage lean-llvm;
  });
  makeOverridableLeanPackage = f:
    let newF = origArgs: f origArgs // {
      overrideArgs = newArgs: makeOverridableLeanPackage f (origArgs // newArgs);
    };
    in lib.setFunctionArgs newF (lib.getFunctionArgs f) // {
      override = args: makeOverridableLeanPackage (f.override args);
    };
  buildLeanPackage = makeOverridableLeanPackage (callPackage (import ./buildLeanPackage.nix) (args // {
    inherit (lean) stdenv;
    lean = lean.stage1;
    inherit (lean.stage1) leanc;
    inherit lean-emacs lean-vscode;
    nix = nix-pinned;
  }));
  lean4-mode = emacsPackages.melpaBuild {
    pname = "lean4-mode";
    version = "1";
    commit = "1";
    src = args.lean4-mode;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash f flycheck magit-section lsp-mode s ];
    recipe = pkgs.writeText "recipe" ''
      (lean4-mode :repo "leanprover/lean4-mode" :fetcher github)
    '';
  };
  lean-emacs = emacsWithPackages [ lean4-mode ];
  # updating might be nicer by building from source from a flake input, but this is good enough for now
  vscode-lean4 = vscode-utils.extensionFromVscodeMarketplace {
      name = "lean4";
      publisher = "leanprover";
      version = "0.0.63";
      sha256 = "sha256-kjEex7L0F2P4pMdXi4NIZ1y59ywJVubqDqsoYagZNkI=";
  };
  lean-vscode = vscode-with-extensions.override {
    vscodeExtensions = [ vscode-lean4 ];
  };
in {
  inherit cc lean4-mode buildLeanPackage vscode-lean4 lean-llvm;
  lean = lean.stage1;
  stage0print-paths = lean.stage1.Lean.print-paths;
  HEAD-as-stage0 = (lean.stage1.Lean.overrideArgs { srcTarget = "..#stage0-from-input.stage0"; srcArgs = "(--override-input lean-stage0 ..\?rev=$(git rev-parse HEAD) -- -Dinterpreter.prefer_native=false \"$@\")"; });
  HEAD-as-stage1 = (lean.stage1.Lean.overrideArgs { srcTarget = "..\?rev=$(git rev-parse HEAD)#stage0"; });
  nix = nix-pinned;
  nixpkgs = pkgs;
  ciShell = writeShellScriptBin "ciShell" ''
    set -o pipefail
    export PATH=${moreutils}/bin:$PATH
    # prefix lines with cumulative and individual execution time
    "$@" |& ts -i "(%.S)]" | ts -s "[%M:%S"
  '';
  vscode = lean-vscode;
} // lean.stage1.Lean // lean.stage1 // lean
