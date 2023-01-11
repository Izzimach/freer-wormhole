--
-- Transformer rules for using Wormhole with the Freer datatype.
-- You specify transformer rules for the basic operations: pure, bind, if/then/else, etc.
--

import Lean
import Lean.Parser

import FreerWormhole.Wormhole
import FreerWormhole.Effects.Freer

open Freer Effect Wormhole

section FreerTransformers

structure FreerTransformers where
    pure : TransformerApp
    bind : TransformerApp
    ifthenelse : TransformerApp
    patMatch : TransformerApp
    effectMatch : TransformerApp


def buildWormholeTransformers : FreerTransformers → List (String × TransformerApp) :=
    fun ft =>
    [
      ⟨"Bind.bind",  ft.bind⟩,
      ⟨"Pure.pure",   ft.pure⟩,
      ⟨"Freer.Impure", ft.effectMatch⟩,
      ⟨"ite",   ft.ifthenelse⟩,
      ⟨"match", ft.patMatch⟩
    ]
  
end FreerTransformers
