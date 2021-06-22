let
  flakePkgs = (import ./default.nix).packages.${builtins.currentSystem};
in { pkgs ? flakePkgs.nixpkgs, llvmPackagesName ? null }:
let llvmPackages = if llvmPackagesName == null
                   then flakePkgs.llvmPackages
                   else pkgs.${"llvmPackages_${llvmPackagesName}"}; in
# use `shell` as default
(attribs: attribs.shell // attribs) rec {
  inherit (flakePkgs) temci;
  shell = pkgs.mkShell.override {
    stdenv = pkgs.overrideCC pkgs.stdenv llvmPackages.clang;
  } rec {
    buildInputs = with pkgs; [
      cmake (gmp.override { withStatic = true; }) ccache temci
      # for llvm-symbolizer
      llvmPackages.bintools
    ];
    # https://github.com/NixOS/nixpkgs/issues/60919
    hardeningDisable = [ "all" ];
    # more convenient `ctest` output
    CTEST_OUTPUT_ON_FAILURE = 1;
    shellHook = ''
      export LEAN_SRC_PATH="$PWD/src"
    '';
  };
  nix = pkgs.mkShell {
    buildInputs = [ flakePkgs.nix ];
    shellHook = ''
      export LEAN_SRC_PATH="$PWD/src"
    '';
  };
}
