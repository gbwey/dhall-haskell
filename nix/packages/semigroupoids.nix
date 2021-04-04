{ mkDerivation, base, base-orphans, bifunctors, Cabal
, cabal-doctest, comonad, containers, contravariant, distributive
, doctest, hashable, stdenv, tagged, template-haskell, transformers
, transformers-compat, unordered-containers
}:
mkDerivation {
  pname = "semigroupoids";
  version = "5.3.4";
  sha256 = "00d2e48973c3ab0a5d52616728ed63d0509454c8328148f698720014d7c58964";
  setupHaskellDepends = [ base Cabal cabal-doctest ];
  libraryHaskellDepends = [
    base base-orphans bifunctors comonad containers contravariant
    distributive hashable tagged template-haskell transformers
    transformers-compat unordered-containers
  ];
  testHaskellDepends = [ base doctest ];
  homepage = "http://github.com/ekmett/semigroupoids";
  description = "Semigroupoids: Category sans id";
  license = stdenv.lib.licenses.bsd3;
}
