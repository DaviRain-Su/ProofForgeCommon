import ProofForge.Core.Codec

/-!
Pure Core schema/codec guards shared by every target repository. Aggregate boundary
extraction, EVM ABI planning, and typed-method guards remain in each target repo.
-/

namespace ProofForgeCoreTests.CoreCodecSpec

open ProofForge.Core.Codec

private def orderBatch : Schema :=
  .record "OrderBatch" #[
    ("market", .scalar .address32),
    ("orders", .boundedArray 4 (.scalar .uint64))
  ]

#guard Scalar.isWellFormed .uint256
#guard Scalar.isWellFormed .boolean
#guard Scalar.isWellFormed (.fixedBytes 32)
#guard !Scalar.isWellFormed (.uint 7)
#guard !Scalar.isWellFormed (.fixedBytes 0)

#guard
  match analyze orderBatch with
  | .ok usage =>
      usage.descriptorNodes == 4 && usage.logicalLeaves == 6 && usage.depth == 3
  | .error _ => false

#guard
  match validate (.record "Bad" #[
      ("same", .scalar .uint64),
      ("same", .scalar .uint64)
    ]) with
  | .error reason => reason.contains "unique"
  | .ok _ => false

#guard
  match validate (.boundedArray 4097 (.scalar .uint64)) with
  | .error reason => reason.contains "capacity"
  | .ok _ => false

#guard
  match analyze (.boundedBytes 16) with
  | .ok usage => usage.descriptorNodes == 2 && usage.logicalLeaves == 17 && usage.depth == 2
  | .error _ => false

#guard
  match analyze (.boundedString 32) with
  | .ok usage => usage.descriptorNodes == 2 && usage.logicalLeaves == 33 && usage.depth == 2
  | .error _ => false

#guard
  match analyze (.enumeration "Side" 8 #[
      ("Bid", .unit),
      ("Ask", .unit)
    ]) with
  | .ok usage => usage.logicalLeaves == 1
  | .error _ => false

private def staticRequest : Schema :=
  .record "Request" #[
    ("amount", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint32, .scalar .boolean]),
    ("levels", .fixedArray 2 (.scalar .uint16))
  ]

#guard
  match staticLeaves staticRequest with
  | .ok leaves =>
      leaves.map StaticLeaf.sourceName ==
        #["amount", "pair_fst", "pair_snd", "levels_0", "levels_1"] &&
      leaves.map (·.type) == #[.uint64, .uint32, .boolean, .uint16, .uint16] &&
      leaves[3]!.path == #[.field "levels", .index 0]
  | .error _ => false

#guard match staticLeaves .unit with
  | .ok leaves => leaves.isEmpty
  | .error _ => false

#guard
  match staticLeaves (.record "Ambiguous" #[
      ("pair_fst", .scalar .uint64),
      ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
    ]) with
  | .ok leaves =>
      leaves.map StaticLeaf.sourceName == #["pair_fst", "pair_fst", "pair_snd"] &&
      leaves[0]!.path != leaves[1]!.path
  | .error _ => false

#guard
  match staticLeaves (.record "Ambiguous" #[
      ("pair_fst", .scalar .uint64),
      ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
    ]) with
  | .error _ => false
  | .ok leaves =>
      match resolveSourceProjection leaves #[1, 1, 1]
          (fun | "w0" => some 0 | _ => none) "pair_fst" with
      | .error reason => reason.contains "missing or ambiguous"
      | .ok _ => false

#guard
  match staticLeaves (.option (.scalar .uint64)) with
  | .error reason => reason.contains "target-owned option tag policy"
  | .ok _ => false

end ProofForgeCoreTests.CoreCodecSpec
