import ProofForge.Core.Math
import ProofForge.Core.FixedPoint

/-!
Host truth tables for the allocation-free bounded, saturating, integer-logarithm,
and square-root Core math. Target extraction behavior is covered in each target
repository's own spec.
-/

namespace Tests.CoreMathSpec

open ProofForge.Core

def u64Max : UInt64 := ~~~(0 : UInt64)

#guard Math.UInt64.min 3 9 == 3
#guard Math.UInt64.min 9 3 == 3
#guard Math.UInt64.max 3 9 == 9
#guard Math.UInt64.max 9 3 == 9
#guard Math.UInt64.average 0 0 == 0
#guard Math.UInt64.average 4 7 == 5
#guard Math.UInt64.average 0 u64Max == 9223372036854775807
#guard Math.UInt64.average u64Max u64Max == u64Max
#guard match Math.UInt64.ceilDiv 0 7 false with
  | .ok value => value == 0
  | _ => false
#guard match Math.UInt64.ceilDiv 9 4 false with
  | .ok value => value == 3
  | _ => false
#guard match Math.UInt64.ceilDiv u64Max 2 false with
  | .ok value => value == 9223372036854775808
  | _ => false
#guard match Math.UInt64.ceilDiv u64Max 1 false with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.ceilDiv 7 0 false with
  | .error false => true
  | _ => false
#guard Math.UInt64.saturatingAdd (u64Max - 1) 1 == u64Max
#guard Math.UInt64.saturatingAdd u64Max 1 == u64Max
#guard Math.UInt64.saturatingAdd 1 u64Max == u64Max
#guard Math.UInt64.saturatingSub 3 7 == 0
#guard Math.UInt64.saturatingSub u64Max 1 == u64Max - 1
#guard Math.UInt64.saturatingMul 0 u64Max == 0
#guard Math.UInt64.saturatingMul u64Max 0 == 0
#guard Math.UInt64.saturatingMul (u64Max / 2) 2 == u64Max - 1
#guard Math.UInt64.saturatingMul (u64Max / 2 + 1) 2 == u64Max
#guard Math.UInt64.log2 0 == 0
#guard Math.UInt64.log2 1 == 0
#guard Math.UInt64.log2 2 == 1
#guard Math.UInt64.log2 3 == 1
#guard Math.UInt64.log2 0x8000000000000000 == 63
#guard Math.UInt64.log2 u64Max == 63
#guard Math.UInt64.log10 0 == 0
#guard Math.UInt64.log10 9 == 0
#guard Math.UInt64.log10 10 == 1
#guard Math.UInt64.log10 9999999999999999999 == 18
#guard Math.UInt64.log10 10000000000000000000 == 19
#guard Math.UInt64.log10 u64Max == 19
#guard Math.UInt64.log256 0 == 0
#guard Math.UInt64.log256 255 == 0
#guard Math.UInt64.log256 256 == 1
#guard Math.UInt64.log256 u64Max == 7
#guard Math.UInt64.sqrt 0 == 0
#guard Math.UInt64.sqrt 1 == 1
#guard Math.UInt64.sqrt 2 == 1
#guard Math.UInt64.sqrt 3 == 1
#guard Math.UInt64.sqrt 4 == 2
#guard Math.UInt64.sqrt 15 == 3
#guard Math.UInt64.sqrt 16 == 4
#guard Math.UInt64.sqrt 17 == 4
#guard Math.UInt64.sqrt 18446744065119617025 == 4294967295
#guard Math.UInt64.sqrt u64Max == 4294967295
#guard Math.UInt64.log2Ceil 0 == 0
#guard Math.UInt64.log2Ceil 1 == 0
#guard Math.UInt64.log2Ceil 2 == 1
#guard Math.UInt64.log2Ceil 3 == 2
#guard Math.UInt64.log2Ceil 4 == 2
#guard Math.UInt64.log2Ceil u64Max == 64
#guard Math.UInt64.log10Ceil 0 == 0
#guard Math.UInt64.log10Ceil 1 == 0
#guard Math.UInt64.log10Ceil 9 == 1
#guard Math.UInt64.log10Ceil 10 == 1
#guard Math.UInt64.log10Ceil 11 == 2
#guard Math.UInt64.log10Ceil 10000000000000000000 == 19
#guard Math.UInt64.log10Ceil u64Max == 20
#guard Math.UInt64.log256Ceil 0 == 0
#guard Math.UInt64.log256Ceil 1 == 0
#guard Math.UInt64.log256Ceil 255 == 1
#guard Math.UInt64.log256Ceil 256 == 1
#guard Math.UInt64.log256Ceil 257 == 2
#guard Math.UInt64.log256Ceil u64Max == 8
#guard Math.UInt64.sqrtCeil 0 == 0
#guard Math.UInt64.sqrtCeil 1 == 1
#guard Math.UInt64.sqrtCeil 2 == 2
#guard Math.UInt64.sqrtCeil 3 == 2
#guard Math.UInt64.sqrtCeil 4 == 2
#guard Math.UInt64.sqrtCeil 15 == 4
#guard Math.UInt64.sqrtCeil 16 == 4
#guard Math.UInt64.sqrtCeil 17 == 5
#guard Math.UInt64.sqrtCeil 18446744065119617025 == 4294967295
#guard Math.UInt64.sqrtCeil 18446744065119617026 == 4294967296
#guard Math.UInt64.sqrtCeil u64Max == 4294967296
#guard match Math.UInt64.mulDiv 10 20 3 false true with
  | .ok value => value == 66
  | _ => false
#guard match Math.UInt64.mulDiv u64Max 2 2 false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDiv u64Max u64Max u64Max false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDiv u64Max u64Max (u64Max - 1) false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDiv ((1 : UInt64) <<< 63) 2 u64Max false true with
  | .ok value => value == 1
  | _ => false
#guard match Math.UInt64.mulDiv ((1 : UInt64) <<< 63) 2 1 false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDiv 7 9 0 false true with
  | .error false => true
  | _ => false
#guard match Math.UInt64.mulDivCeil 10 20 3 false true with
  | .ok value => value == 67
  | _ => false
#guard match Math.UInt64.mulDivCeil u64Max 2 2 false true with
  | .ok value => value == u64Max
  | _ => false
#guard match Math.UInt64.mulDivCeil 6 15372286728091293013 5 false true with
  | .error true => true
  | _ => false
#guard match Math.UInt64.mulDivCeil 7 9 0 false true with
  | .error false => true
  | _ => false
#guard match FixedPoint.UInt64.mulDown 150 25 100 1 2 with
  | .ok value => value == 37
  | _ => false
#guard match FixedPoint.UInt64.mulUp 150 25 100 1 2 with
  | .ok value => value == 38
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 30 100 1 2 3 with
  | .ok value => value == 336
  | _ => false
#guard match FixedPoint.UInt64.divUp 101 30 100 1 2 3 with
  | .ok value => value == 337
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 0 0 1 2 3 with
  | .error 1 => true
  | _ => false
#guard match FixedPoint.UInt64.divDown 101 0 100 1 2 3 with
  | .error 2 => true
  | _ => false
#guard match FixedPoint.UInt64.mulDown u64Max u64Max 1 1 2 with
  | .error 2 => true
  | _ => false

private def mulDivSamples : List UInt64 :=
  [0, 1, 2, 3, 7, 31, 0xffffffff, 0x100000000,
    0x7fffffffffffffff, 0x8000000000000000, u64Max - 1, u64Max]

private def validMulDiv (left right denominator : UInt64) : Bool :=
  let result := Math.UInt64.mulDiv left right denominator false true
  if denominator == 0 then
    match result with
    | .error false => true
    | _ => false
  else
    let quotient := (left.toNat * right.toNat) / denominator.toNat
    if u64Max.toNat < quotient then
      match result with
      | .error true => true
      | _ => false
    else
      match result with
      | .ok value => value.toNat == quotient
      | _ => false

#guard mulDivSamples.all fun left =>
  mulDivSamples.all fun right =>
    mulDivSamples.all fun denominator => validMulDiv left right denominator

private def validMulDivCeil (left right denominator : UInt64) : Bool :=
  let result := Math.UInt64.mulDivCeil left right denominator false true
  if denominator == 0 then
    match result with
    | .error false => true
    | _ => false
  else
    let product := left.toNat * right.toNat
    let quotient := (product + denominator.toNat - 1) / denominator.toNat
    if u64Max.toNat < quotient then
      match result with
      | .error true => true
      | _ => false
    else
      match result with
      | .ok value => value.toNat == quotient
      | _ => false

#guard mulDivSamples.all fun left =>
  mulDivSamples.all fun right =>
    mulDivSamples.all fun denominator => validMulDivCeil left right denominator

private def validFloorRoot (value : UInt64) : Bool :=
  let root := Math.UInt64.sqrt value
  if value == 0 then root == 0
  else root ≤ value / root && value / (root + 1) < root + 1

#guard (List.range 4096).all fun value => validFloorRoot (UInt64.ofNat value)
#guard validFloorRoot 0x7fffffffffffffff
#guard validFloorRoot 0x8000000000000000
#guard validFloorRoot u64Max

private def validCeilRoot (value : UInt64) : Bool :=
  let root := Math.UInt64.sqrtCeil value
  if value == 0 then root == 0
  else
    let lower := root - 1
    lower * lower < value && (root == 4294967296 || value ≤ root * root)

#guard (List.range 4096).all fun value => validCeilRoot (UInt64.ofNat value)
#guard validCeilRoot 0x7fffffffffffffff
#guard validCeilRoot 0x8000000000000000
#guard validCeilRoot u64Max

end Tests.CoreMathSpec
