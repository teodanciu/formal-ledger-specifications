{ sources ? import ./nix/sources.nix
, pkgs ? import sources.nixpkgs {
    overlays = [ ];
    config = { };
  }
}:

with pkgs;
let
  customAgda = import sources.agda-nixpkgs {};

  agdaStdlib = customAgda.agdaPackages.standard-library.overrideAttrs (oldAttrs: {
    version = "1.7.2";
    src = fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "668f0bbd498cfae253605fd7132c3b9ed52cc4ac";
      sha256 = "4jNFpDtVWecwpuzZMtQb0kJ9s4LkjBYx+1c0n/Ft9tw=";
    };
  });

  agdaStdlibMeta = customAgda.agdaPackages.mkDerivation {
    pname = "agda-stdlib-meta";
    version = "0.1";
    src = fetchFromGitHub {
      repo = "stdlib-meta";
      owner = "omelkonian";
      rev = "761f81753b588d865b45acb44683b1b4042d78c0";
      sha256 = "iGdZv18Ku+GZ+MikQWwWYv8vs8j59OXRB1xqYTmoqAc=";
    };
    patches = [ ./stdlib-meta-update-imports.patch ];
    meta = { };
    libraryFile = "stdlib-meta.agda-lib";
    everythingFile = "Main.agda";
    buildInputs = [ agdaStdlib ];
  };

  deps = [ agdaStdlib agdaStdlibMeta ];
  agdaWithPkgs = p: customAgda.agda.withPackages { pkgs = p; ghc = pkgs.ghc; };

in
rec {

  # agda  = agdaWithPkgs deps;
  # agda2 = agdaWithPkgs [ agdaStdlib ];           # for working on stdlib-meta
  # agda3 = agdaWithPkgs (deps ++ [ agdaLedger ]); # for using ledger as a library

  agdaLedger = customAgda.agdaPackages.mkDerivation {
    pname = "Agda-ledger";
    version = "0.1";
    src = ./src;
    meta = { };
    buildInputs = deps;
    postInstall = ''
      cp -r latex $out
      sh checkTypeChecked.sh
      '';
    extraExtensions = [ "hs" "cabal" ];
  };

  # a parameterized attribute set containing derivations for: 1) executable spec 2) docs
  specsDerivations = { dir, agdaLedgerFile, hsMainFile, doc }:
    let
      hsSrc =
        stdenv.mkDerivation {
          pname = "Agda-ledger-${dir}-hs-src";
          version = "0.1";
          src = "${agdaLedger}";
          meta = { };
          buildInputs = [ (agdaWithPkgs deps) ];
          buildPhase = "";
          installPhase = ''
            mkdir -p $out
            agda -c --ghc-dont-call-ghc --compile-dir $out ${dir}/${agdaLedgerFile}
            cp ${dir}/${hsMainFile} $out
            cp ${dir}/agda-ledger-executable-spec.cabal $out
            # Append all the modules generated by MAlonzo to the cabal file
            find $out/MAlonzo -name "*.hs" -print | sed "s#^$out/#        #;s#\.hs##;s#/#.#g" >> $out/agda-ledger-executable-spec.cabal
          '';
        };
      docs = stdenv.mkDerivation {
        pname = "${dir}-docs";
        version = "0.1";
        src = "${agdaLedger}";
        meta = { };
        buildInputs = [
          (agdaWithPkgs deps)
          (texlive.combine {
            inherit (texlive)
              scheme-small
              xits
              collection-latexextra
              collection-latexrecommended
              collection-mathscience
              bclogo
              latexmk;
          })
        ];
        buildPhase = ''
          find ${dir} -name \*.lagda -exec agda --latex {} \;
          cd latex && latexmk -xelatex ${dir}/${doc}.tex && cd ..
        '';
        installPhase = ''
          mkdir -p $out
          agda --html --html-dir $out/html ${dir}/${doc}.lagda
          cp latex/${doc}.pdf $out
        '';
      };
    in
    {
      executableSpecSrc = hsSrc;
      executableSpec = haskellPackages.callCabal2nix "Agda-ledger-executable-spec" "${hsSrc}" { };
      docs = docs;
    };

  ledger = specsDerivations {
    dir = "Ledger";
    agdaLedgerFile = "Foreign/HSLedger.agda";
    hsMainFile = "HSLedgerTest.hs";
    doc = "PDF";
  };
  midnight = specsDerivations {
    dir = "MidnightExample";
    agdaLedgerFile = "HSLedger.agda";
    hsMainFile = "Main.hs";
    doc = "PDF";
  };
}
