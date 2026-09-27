module mpat-lib

// Helper for mpat.kk: a small cross-module inlineable function with a
// multi-scrutinee match. Its branch patterns are emitted into the .kki
// inline-definition section; parsing them back must preserve the pattern
// order (Core.Pretty.prettyPatterns once emitted them reversed, so
// cross-module inlining swapped the scrutinees).
//
// This module is precompiled in test/Spec.hs (before the parallel test phase,
// like bankers.kk) so mpat.kk deterministically loads it from the .kki.
pub type dir
  North
  East(i : int)
  South
  West(i : int)

pub fun cross( d1 : dir, d2 : dir ) : bool
  match (d1, d2)
    (North, _)          -> True
    (East(_), East(_))  -> True
    _                   -> False

pub fun main()
  println( cross(North, South) )
