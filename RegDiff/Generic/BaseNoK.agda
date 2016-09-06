open import Prelude
open import Prelude.Vector

{-
  This is just a proxy import in case we do
  not want constants in our type.
-}

module RegDiff.Generic.BaseNoK where

  open import RegDiff.Generic.Base []
    renaming (U to U₀)
    public
