module

public import Clean.Air.CountedChannel
public import Clean.Air.OrderedChannel

@[expose] public section

/-!
# A range check pulled with multiplicity

A row that needs the same fact twice can pull it twice, or pull it once with multiplicity `2`. The
second costs one interaction instead of two, and is what `Channel.counted` is for.

Here the fact is `value < 256`. `byteChannel.counted 2` hands its guarantee to a pull of
multiplicity `1` or `2`, and asks such a pull to say which: that obligation is what the consumer
discharges by constraining its count, and it is what makes the channel sound. Under
`Balance.logUpUpTo 2` the pull is matched by a push, so the guarantee comes from the provider's
requirement.
-/

namespace CountedBytes

open Air.Flat

variable {p : ℕ} [Fact p.Prime] [pGt : Fact (p > 512)]

/-- Pulls may count up to `2`. -/
abbrev N : ℕ := 2

/-- The bytes, read with multiplicity. -/
def byteChannel : Channel (F p) field where
  name := "counted-bytes"
  Guarantees value _ := value.val < 256

omit pGt in
/-- A count of `1` or `2` is a count up to `2`. This is the step that turns a field constraint into
the channel's `CountUpTo`, and it is the only arithmetic the example needs. -/
lemma countUpTo_of_one_or_two {c : F p} (h : (c - 1) * (c - 2) = 0) : CountUpTo N c := by
  rcases mul_eq_zero.mp h with h | h <;> rw [sub_eq_zero] at h
  · exact ⟨1, le_rfl, by norm_num, by simp [h]⟩
  · exact ⟨2, by norm_num, le_rfl, by simp [h]⟩

structure ProviderInput (F : Type) where
  value : F
  /-- how many pulls this row answers -/
  mult : F
deriving ProvableStruct

/-- One table row: pushes its byte as often as it is pulled. -/
def provider : GeneralFormalCircuit (F p) ProviderInput unit where
  name := "counted-bytes-provider"
  main input := byteChannel.emitUpTo N input.mult input.value

  channelsWithRequirements := [byteChannel.counted N]
  Assumptions input _ := input.value.val < 256
  ProverAssumptions input _ _ := input.value.val < 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [byteChannel]
    simp_all
  completeness := by
    circuit_proof_start [byteChannel]

structure ConsumerInput (F : Type) where
  value : F
  /-- how many times this row needs the fact: `1` or `2` -/
  count : F
deriving ProvableStruct

/-- A row that needs `value < 256` once or twice, and pulls it once with that multiplicity.

The constraint on `count` is not bookkeeping: it is what discharges the pull's requirement
`count = 0 ∨ CountUpTo 2 count`. Without it the row could claim any multiplicity, and
`Channel.counted_not_consistent` shows the channel would then be unsound. -/
def consumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "counted-bytes-consumer"
  main input := do
    assertZero ((input.count - 1) * (input.count - 2))
    byteChannel.pullUpTo N input.count input.value

  Spec input _ _ := input.value.val < 256
  ProverAssumptions input _ _ := (input.count = 1 ∨ input.count = 2) ∧ input.value.val < 256

  requirementsChannelsLawful := by
    simp only [circuit_norm, seval]
    intro input env h
    exact .inr (countUpTo_of_one_or_two h)

  soundness := by
    circuit_proof_start [byteChannel]
    obtain ⟨h_count, h_guarantee⟩ := h_holds
    have h_in := countUpTo_of_one_or_two h_count
    exact ⟨h_guarantee h_in, .inr h_in⟩
  completeness := by
    circuit_proof_start [byteChannel]
    obtain ⟨h_count, h_value⟩ := h_assumptions
    refine ⟨?_, fun _ => h_value⟩
    rcases h_count with h | h <;> simp [h]

end CountedBytes
