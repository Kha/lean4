let drv = { stdenv, lib, runCommand, cmake, coreutils, python, gmp }:

with builtins;
let
  stage = desc: prevStdlibExp: rec {
    leanBin = stdenv.mkDerivation rec {
      name = "lean-${desc}";

      src = builtins.filterSource (p: t: builtins.match "src.*|bin.*|library|library/Makefile.in" (lib.removePrefix (toString ./. + "/") p) != null && !(lib.hasSuffix "stage0" p)) ./.;

      # HACK: https://github.com/NixOS/nixpkgs/issues/62121
      CCACHE_DIR = "/var/cache/ccache";
      nativeBuildInputs = [ cmake python ];
      buildInputs = [ gmp ];
      enableParallelBuilding = true;

      preConfigure = ''
        cd src
        #cp -r --reflink=auto --no-preserve=mode ${prevStdlibExp} stage0
        ln -s ${prevStdlibExp} stage0
      '';
      postConfigure = ''
        patchShebangs ../../bin
      '';
      buildFlags = [ "bin_lean_stage0" ];
      installPhase = ''
        mkdir $out
        cp -r ../../bin $out
      '';
    };
    # "init.core" ~> "init/core.lean"
    modToLean = mod: replaceStrings ["."] ["/"] mod + ".lean";
    # "init.core" ~> ./library/init/core.lean
    modToLocalLean = mod: ./library + ("/" + modToLean mod);
    # build a file containing the module names of all immediate dependencies of `mod`
    leanDeps = mod: runCommand "${mod}-deps" {
      src = [ (modToLocalLean mod) ];
      preferLocalBuild = true;
      allowSubstitutes = false;
    } ''
      sed -En 's/^import (.*)/\1/p' < $src | tr " " "\n" > $out
    '';
    # build module (.olean and .cpp) given derivations of all (transitive) dependencies
    buildMod = mod: deps: stdenv.mkDerivation rec {
      name = "${mod}-${desc}";
      relpath = modToLean mod;
      src = [ (modToLocalLean mod) ];
      LEAN_PATH = lib.concatStringsSep ":" (["."] ++ deps);
      buildCommand = ''
        mkdir -p $out/$(dirname $relpath)
        cd $out
        cp --reflink=auto $src $relpath
        ${leanBin}/bin/lean --make --cpp=''${relpath%.lean}.cpp $relpath
      '';
    };
    singleton = name: value: listToAttrs [ { inherit name value; } ];
    # `init.control` ~> `init.control.default`
    normalizeMod = mod: if lib.pathIsDirectory (./library + ("/" + replaceStrings ["."] ["/"] mod)) then mod + ".default" else mod;
    # Recursively build `mod` and its dependencies. `modMap` maps module names to
    # `{ deps, drv }` pairs of a derivation and its transitive dependencies (as a nested
    # mapping from module names to derivations). It is passed linearly through the
    # recursion to memoize common dependencies.
    buildModAndDeps' = mod: modMap: if modMap ? ${mod} then modMap else
      let
        immDeps = map normalizeMod (filter (p: p != "") (lib.splitString "\n" (readFile (leanDeps mod))));
        modMap' = lib.foldr buildModAndDeps' modMap immDeps;
      in modMap' // singleton mod rec {
        deps = lib.foldr (dep: depMap: depMap // modMap'.${dep}.deps // singleton dep modMap'.${dep}.drv) {} immDeps;
        drv = buildMod mod (attrValues deps);
      };
    buildModAndDeps = mod: let mod' = normalizeMod mod; in buildModAndDeps' mod' {};
    modMap = buildModAndDeps' "init.lean.default" (buildModAndDeps "init");
    stdlib = stdenv.mkDerivation {
      name = "lean-stdlib-${desc}";
      buildCommand = ''
        mkdir $out
        cp -rs --no-preserve=mode ${lib.concatStringsSep " " (map (v: v.drv + "/*") (attrValues modMap))} $out/
        echo "add_library (stage0 OBJECT $(cd $out; find . -name '*.cpp' | sort))" > $out/CMakeLists.txt
      '';
    };
  };
  stage1 = stage "stage1" ./src/stage0;
  stage2 = stage "stage2" stage1.stdlib;
  stage3 = stage "stage3" stage2.stdlib;
in stage3.leanBin

;
in with import <nixpkgs> {}; callPackage drv { stdenv = ccacheStdenv; }
