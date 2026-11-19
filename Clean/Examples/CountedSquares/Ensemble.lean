module

public import Clean.Air.CountedChannel
public import Clean.Air.OrderedChannel
public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# A fact pulled with multiplicity

A row that needs the same fact twice can pull it twice, or, with `Channel.counted`, pull it once
with multiplicity `2`: one interaction instead of two.

The fact here is `y = x * x`. The squaring chip enforces it with a constraint and pushes the pair;
a consumer that needs the square once or twice pulls it once with that multiplicity.

Two things make `squares.counted 2` sound. A pull must have multiplicity `0`, `1` or `2`, which the
consumer discharges by constraining its count: a row free to claim any multiplicity could pull at
`-1`, which field sums count as a push of a pair nobody checked. And the balance check must match
pulls of multiplicity `2` with a push: under plain `BalancedInteractions` the counted channel is not
consistent (`Channel.counted_not_consistent`), so the ensemble uses `Balance.logUpUpTo 2`.

Generation starts from the four provider rows, each pushing once through the `+ 1` of the provider's
emit, since a multiplicity cell starts at `0`; two consumer rows answer them at multiplicity `2`. A
VM seeds its channels from the verifier instead, as in `Clean/Examples/FemtoCairo/FlatAir.lean`.
`Clean/Examples/CountedSquares/WitnessGenerationTest.lean` runs it.

Generation tallies a counted pull as the natural number its multiplicity claims
(`Tally.signedCount`), but does not split a row at `N`. A demand component with a multiplicity cell
keeps one row per message (`DemandMode.answer`), so if it also pulled with that count, a message
demanded more than `N` times would get a row whose counted pull fails its constraint. The consumer
here pulls a fixed count per row instead.

For a large `N`, a chip would range-check its count on another channel rather than constrain it
with a polynomial, which needs several channels finished in order rather than the single one here,
as in `Clean/Examples/RangeCheckedCount.lean`.
-/

namespace CountedSquares

open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- Pulls may count up to `2`. -/
abbrev N : ℕ := 2

/-- Pairs `(x, y)` with `y = x * x`. -/
def squares : Channel (F p) (ProvablePair field field) where
  name := "squares"
  Guarantees | (x, y), _ => y = x * x

/-- The consumer's constraint on its count gives the channel's `CountUpTo 2`. -/
lemma countUpTo_of_sub_one_mul_sub_two_eq_zero {c : F p} (h : (c - 1) * (c - 2) = 0) :
    CountUpTo N c := by
  rcases mul_eq_zero.mp h with h | h <;> rw [sub_eq_zero] at h
  · exact ⟨1, le_rfl, by norm_num, by simp [h]⟩
  · exact ⟨2, by norm_num, le_rfl, by simp [h]⟩

structure ProviderInput (F : Type) where
  x : F
  y : F
  /-- the row pushes `mult + 1` times -/
  mult : F
deriving ProvableStruct

/-- The squaring chip: constrains `y = x * x`, which pays for the guarantee its push owes, and
pushes `(x, y)` with multiplicity `mult + 1`.

The `+ 1` seeds generation, where a multiplicity cell starts at `0`. It is field arithmetic, not a
count: a row with `mult = -1` pushes nothing, which soundness allows, since only a push owes the
guarantee. -/
def provider : GeneralFormalCircuit (F p) ProviderInput unit where
  name := "squares-provider"
  main input := do
    input.y === input.x * input.x
    squares.emitUpTo N (input.mult + 1) (input.x, input.y)

  channelsWithRequirements := [squares.counted N]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.y = input.x * input.x

  soundness := by
    circuit_proof_start [squares]
    simp_all
  completeness := by
    circuit_proof_start [squares]
    simp_all

structure ConsumerInput (F : Type) where
  x : F
  y : F
  /-- how many times this row needs the fact: `1` or `2` -/
  count : F
deriving ProvableStruct

/-- A row that needs `y = x * x` once or twice, and pulls it once with that multiplicity.

The constraint on `count` discharges the pull's requirement `count = 0 ∨ CountUpTo 2 count`. -/
def consumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "squares-consumer"
  main input := do
    assertZero ((input.count - 1) * (input.count - 2))
    squares.pullUpTo N input.count (input.x, input.y)

  Spec input _ _ := input.y = input.x * input.x
  ProverAssumptions input _ _ :=
    (input.count = 1 ∨ input.count = 2) ∧ input.y = input.x * input.x

  requirementsChannelsLawful := by
    simp only [circuit_norm, seval]
    intro input env h
    exact .inr (countUpTo_of_sub_one_mul_sub_two_eq_zero h)

  soundness := by
    circuit_proof_start [squares]
    obtain ⟨h_count, h_guarantee⟩ := h_holds
    have h_in := countUpTo_of_sub_one_mul_sub_two_eq_zero h_count
    exact ⟨h_guarantee h_in, .inr h_in⟩
  completeness := by
    circuit_proof_start [squares]
    obtain ⟨h_count, h_square⟩ := h_assumptions
    refine ⟨?_, fun _ => h_square⟩
    rcases h_count with h | h <;> simp [h]

/-- Four rows for the square `4 = 2 * 2`, present before any demand so that generation can start:
each pushes once through the circuit's `+ 1`, and the multiplicity cell counts further pulls.

`x` and `y` are witness cells, not fixed columns: a fixed column is a value the verifier knows, and
the verifier knowing `y` would make `y = x * x` true of the table without the push carrying it. -/
abbrev providerComponent : Component (F p) where
  circuit := provider
  generation := .preallocated {
    trigger := .pull
    channel := squares
    height := 4
    input _ := pure { x := .witness 2, y := .witness 4, mult := .multiplicity }
    rowOf _ := 0
  }

/-- While a pushed square is unanswered, a new row pulls it at multiplicity `2`, so two rows answer
the provider's four pushes. Their `x` and `y` come from the message, so what makes `y = x * x` true
of a consumer row is the channel and the provider's constraint, nothing local.

Rows of this component are active: outside characteristic `2`, the default padding of `0` fails
`(count - 1) * (count - 2) = 0`. The padding row pulls `(2, 4)` at multiplicity `1`, and the
generator answers that pull by raising a provider multiplicity. A chip whose rows may be idle would
pad with `count = 0`, the other branch of the pull's requirement, instead. -/
abbrev consumerComponent : Component (F p) where
  circuit := consumer
  generation := .demand {
    channel := squares
    trigger := .push
    input | (x, y) => pure { x, y, count := .witness 2 }
    padding := { x := 2, y := 4, count := 1 }
  }

/-- The counted channel, the chip that serves it, the channel marked finished, and the chip that
reads it. `markFinished` is where instance search needs
`(squares.counted N).ConsistentUpTo (Balance.logUpUpTo N).pullBound`. -/
def soundEnsemble : SoundEnsemble (F p) unit (Balance.logUpUpTo N) :=
  SoundEnsemble.empty (F p) unit (Balance.logUpUpTo N)
  |>.addChannel (squares.counted N)
  |>.addTable providerComponent
      (by simp [circuit_norm, provider])
      (by simp [circuit_norm, provider])
      (by simp [circuit_norm, provider])
  |>.markFinished (squares.counted N)
  |>.addTable consumerComponent
      (by simp [circuit_norm, consumer])
      (by simp [circuit_norm, consumer])
      (by simp [circuit_norm, consumer, provider])

/-- Every table's spec holds under `Balance.logUpUpTo 2`, including the consumer's `y = x * x`,
which it reads from a pull of multiplicity `2`. The price is in `fits`: `Ensemble.Statement`
requires each channel's interaction count times `2` to be below the characteristic. -/
theorem tableSoundness :
    (soundEnsemble (p := p)).ensemble.TableSoundness (Balance.logUpUpTo N) :=
  Ensemble.tableSoundness_of_soundChannels
    ⟨_, (soundEnsemble (p := p)).finished_subset, (soundEnsemble (p := p)).soundChannels⟩

end CountedSquares
