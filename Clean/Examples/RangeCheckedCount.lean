module

public import Clean.Air.CountedChannel
public import Clean.Air.Lookup
public import Clean.Air.OrderedChannel
public import Clean.Air.StagedChannels

@[expose] public section

/-!
# A count range-checked on another channel

`CountedSquares` constrains its count arithmetically, which only scales to a small bound. Here a
row needs a fact up to `255` times, pulls it once with that multiplicity, and range-checks the
multiplicity by pulling it from a byte table. The requirement the counted pull owes,
`count = 0 ∨ CountUpTo 255 count`, then follows from the row's guarantee on `bytes`, not from its
constraints.

`OrderedChannel` cannot order this ensemble: the consumer both pulls from `doubles` and owes
requirements on it, which `OrderedChannelRefl` rules out. A finishing order of channels can:
`tableSoundness` finishes `bytes` before `doubles` through
`Ensemble.tableSoundness_of_stagedRequirements`. Witness generation is not exercised; each
component declares one only because `Component` requires it.

The last two sections add a verifier to the same tables: one that pulls its public input from
`bytes`, and one that also pushes it to a further channel, which owes a requirement that its
guarantee on `bytes` pays for.
-/

namespace RangeCheckedCount

open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- The bytes `0, ..., 255`, for range checks. -/
def bytes : Lookup (F p) field where
  name := "bytes"
  height := 256
  row i := pure i
  rowOf value := value.val
  Contains value := value.val < 256
  contains_iff value := by
    simp only [circuit_norm, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    constructor
    · intro h
      refine ⟨value.val.toUInt64, ?_, ?_⟩ <;> simp [h]
    · rintro ⟨i, hi, rfl⟩
      rwa [ZMod.val_cast_of_lt (by linarith [(‹Fact (p > 512)›).out])]

/-- Pairs `(x, y)` with `y = x + x`. -/
def doubles : Channel (F p) (ProvablePair field field) where
  name := "doubles"
  Guarantees | (x, y), _ => y = x + x

omit [Fact (p > 512)] in
/-- A byte is `0` or a count up to `255`: the step from the byte table's guarantee to the
requirement of a counted pull. -/
lemma eq_zero_or_countUpTo_of_val_lt {count : F p} (h : count.val < 256) :
    count = 0 ∨ CountUpTo 255 count := by
  by_cases h0 : count = 0
  · exact .inl h0
  · exact .inr (countUpTo_of_ne_zero_of_val_le h0 (by omega))

lemma bytes_ne_doubles : (bytes (p := p)).channel.toRaw ≠ doubles.counted 255 := fun h => by
  have := congrArg RawChannel.name h
  simp [bytes, doubles, circuit_norm] at this

structure DoublerInput (F : Type) where
  x : F
  y : F
  /-- how many pulls this row answers, counted with multiplicity -/
  mult : F
deriving ProvableStruct

/-- The doubling chip: constrains `y = x + x`, which every active push of the pair owes. -/
def doubler : GeneralFormalCircuit (F p) DoublerInput unit where
  name := "doubler"
  main input := do
    input.y === input.x + input.x
    doubles.emitUpTo 255 input.mult (input.x, input.y)
  channelsWithRequirements := [doubles.counted 255]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.y = input.x + input.x
  soundness := by
    circuit_proof_start [doubles]
    simp_all
  completeness := by
    circuit_proof_start [doubles]
    simp_all

/-- One row per distinct pair pulled from `doubles`, its multiplicity the total pulled count. -/
abbrev doublerComponent : Component (F p) where
  circuit := doubler
  generation := .demand {
    trigger := .pull
    channel := doubles
    input | (x, y) => pure { x, y, mult := .multiplicity }
  }

structure ConsumerInput (F : Type) where
  x : F
  y : F
  /-- how many times this row needs the fact -/
  count : F
deriving ProvableStruct

/-- A row that needs `y = x + x` up to `255` times and pulls it once with that multiplicity, which
only its pull from `bytes` bounds. -/
def consumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "consumer"
  main input := do
    bytes.channel.pull input.count
    doubles.pullUpTo 255 input.count (input.x, input.y)
  channelsWithRequirements := [doubles.counted 255]
  Spec input _ _ := input.count ≠ 0 → input.y = input.x + input.x
  ProverAssumptions input _ _ := input.count.val < 256 ∧ input.y = input.x + input.x
  soundness := by
    circuit_proof_start [bytes, doubles]
    obtain ⟨h_byte, h_double⟩ := h_holds
    have h_count := eq_zero_or_countUpTo_of_val_lt h_byte
    refine ⟨fun h0 => ?_, h_count⟩
    rcases h_count with h | h
    · exact absurd h h0
    · exact h_double h
  completeness := by
    circuit_proof_start [bytes, doubles]
    simp_all

/-- One consumer row per pair pushed to `doubles` that nothing has pulled. -/
abbrev consumerComponent : Component (F p) where
  circuit := consumer
  generation := .demand {
    trigger := .push
    channel := doubles
    input | (x, y) => pure { x, y, count := .witness 1 }
  }

/-- `OrderedChannel` cannot take the consumer: it pulls from `doubles` and owes on it. -/
example :
    ¬ OrderedChannelRefl (doubles.counted 255 : RawChannel (F p)) (consumerComponent (p := p)) := by
  simp [circuit_norm, consumer]

/-- The consumer's requirement on `doubles`, from its guarantee on `bytes` alone. Neither
`Component.requirementsAfter_of_not_mem` nor `Component.requirementsAfter_of_guarantees_subset`
gives it: the consumer owes on `doubles` and has guarantees on it. -/
theorem consumer_requirementsAfter : (consumerComponent (p := p)).RequirementsAfter
    (doubles.counted 255) [bytes.channel.toRaw] := by
  rintro table h_comp - - guarantees row h_row
  have h_bytes := guarantees _ List.mem_cons_self row h_row
  rw [h_comp] at h_bytes ⊢
  simp only [Component.interactions_eq, Component.rowOperations, circuit_norm, consumer]
    at h_bytes ⊢
  exact eq_zero_or_countUpTo_of_val_lt h_bytes.1

/-- The ensemble: the byte table, the doubling chip, and the consumer. -/
def ensemble : Ensemble (F p) unit where
  tables := [consumerComponent, doublerComponent, bytes.component]
  unique_names := by simp [circuit_norm, consumer, doubler, bytes]
  channels := [doubles.counted 255, bytes.channel.toRaw]
  unique_channel_names := by simp [circuit_norm, bytes, doubles]
  tables_channels := by simp [circuit_norm, consumer, doubler, bytes]
  verifier_channels := by simp [circuit_norm]

/-- `bytes` finished before `doubles`. -/
abbrev finished : List (RawChannel (F p)) := [doubles.counted 255, bytes.channel.toRaw]

/-- Each component's requirements on `doubles` follow from its guarantees on `bytes`, and its
requirements on `bytes` hold unconditionally. -/
theorem stagedRequirements :
    ∀ component ∈ (ensemble (p := p)).tables, component.StagedRequirements finished := by
  simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    circuit_norm]
  refine ⟨⟨consumer_requirementsAfter, Component.requirementsAfter_of_not_mem _
      (by simp [circuit_norm, consumer, bytes_ne_doubles])⟩,
    ⟨Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm, doubler]),
      Component.requirementsAfter_of_not_mem _
        (by simp [circuit_norm, doubler, bytes_ne_doubles])⟩,
    ⟨Component.requirementsAfter_of_not_mem _ (by simp [circuit_norm, bytes_ne_doubles.symm]),
      Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm])⟩⟩

/-- Every channel a component has guarantees on is finished. -/
theorem guarantees_subset_finished : ∀ component ∈ (ensemble (p := p)).tables,
    component.circuit.channelsWithGuarantees ⊆ finished := by
  simp [ensemble, circuit_norm, consumer, doubler, bytes]

/-- Every table is sound under `Balance.logUpUpTo 255`, with `bytes` finished before `doubles`. -/
theorem tableSoundness : (ensemble (p := p)).TableSoundness (Balance.logUpUpTo 255) := by
  apply Ensemble.tableSoundness_of_stagedRequirements finished (List.Subset.refl _)
    (verifier_subset_finished := by simp [ensemble, circuit_norm, Verifier.Program.empty])
    (verifier_staged := Ensemble.verifierStagedRequirementsOn_of_verifier_empty rfl _)
    (staged := stagedRequirements) guarantees_subset_finished
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨inferInstance, inferInstance⟩

/-! ## With a verifier

The same tables, with a verifier that pulls its public input from `bytes`. Its spec, that the input
is a byte, is the guarantee of that pull, which the `bytes` stage gives it as it gives the tables
theirs. -/

/-- Pulls the public input from `bytes`. -/
def byteVerifier : Verifier.Program (F p) field where
  main x := Verifier.pull bytes.channel x
  Spec x _ := x.val < 256
  soundness := by simp_all [circuit_norm, bytes]

/-- `ensemble` with `byteVerifier`. -/
def ensembleWithVerifier : Ensemble (F p) field where
  tables := (ensemble (p := p)).tables
  unique_names := (ensemble (p := p)).unique_names
  channels := (ensemble (p := p)).channels
  unique_channel_names := (ensemble (p := p)).unique_channel_names
  tables_channels := (ensemble (p := p)).tables_channels
  verifier := byteVerifier
  verifier_channels := by simp [ensemble, circuit_norm, byteVerifier, bytes]

/-- The tables and the verifier's spec are sound under `Balance.logUpUpTo 255`. -/
theorem tableSoundness_withVerifier :
    (ensembleWithVerifier (p := p)).TableSoundness (Balance.logUpUpTo 255) := by
  apply Ensemble.tableSoundness_of_stagedRequirements (ens := ensembleWithVerifier) finished
    (List.Subset.refl _)
    (verifier_subset_finished := by simp [ensembleWithVerifier, circuit_norm, byteVerifier, bytes])
    (verifier_staged := Ensemble.verifierStagedRequirementsOn_of_not_mem
      (by simp [ensembleWithVerifier, circuit_norm, byteVerifier, bytes]))
    (staged := stagedRequirements) guarantees_subset_finished
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨inferInstance, inferInstance⟩

/-! ## A verifier that pushes

A verifier's push owes the channel's guarantee for a value of the public input, which holds only if
something establishes it. Here the verifier first pulls its input from `bytes`, then pushes it to
`seenBytes`, whose guarantee is that the value is a byte, and a table pulls it from there. That
table's spec rests on the verifier's push, whose requirement on the `seenBytes` stage follows from
its guarantee on the earlier `bytes` stage, as a table's would. -/

/-- Values known to be bytes. -/
def seenBytes : Channel (F p) field where
  name := "seen-bytes"
  Guarantees x _ := x.val < 256

omit [Fact (p > 512)] in
lemma seenBytes_ne_doubles : (seenBytes (p := p)).toRaw ≠ doubles.counted 255 := fun h => by
  have := congrArg RawChannel.name h
  simp [seenBytes, doubles, circuit_norm] at this

lemma seenBytes_ne_bytes : (seenBytes (p := p)).toRaw ≠ bytes.channel.toRaw := fun h => by
  have := congrArg RawChannel.name h
  simp [seenBytes, bytes, circuit_norm] at this

/-- Pulls the public input from `bytes`, then pushes it to `seenBytes`. -/
def forwardingVerifier : Verifier.Program (F p) field where
  main x := do
    Verifier.pull bytes.channel x
    Verifier.push seenBytes x
  Spec x _ := x.val < 256
  soundness := by simp_all [circuit_norm, bytes]

/-- Pulls a value from `seenBytes`, and so knows it is a byte. -/
def seenReader : GeneralFormalCircuit (F p) field unit where
  name := "seen-reader"
  main x := seenBytes.pull x
  Spec x _ _ := x.val < 256
  ProverAssumptions x _ _ := x.val < 256
  soundness := by
    circuit_proof_start [seenBytes]
    simp_all
  completeness := by
    circuit_proof_start [seenBytes]
    exact h_assumptions

/-- One row per value pushed to `seenBytes` that nothing has pulled. -/
abbrev seenReaderComponent : Component (F p) where
  circuit := seenReader
  generation := .demand {
    trigger := .push
    channel := seenBytes
    input x := pure x
  }

/-- `ensemble` with `seenReaderComponent`, `forwardingVerifier`, and the channel between them. -/
def ensembleWithForwardingVerifier : Ensemble (F p) field where
  tables := seenReaderComponent :: (ensemble (p := p)).tables
  unique_names := by simp [ensemble, circuit_norm, seenReader, consumer, doubler, bytes]
  channels := seenBytes.toRaw :: (ensemble (p := p)).channels
  unique_channel_names := by simp [ensemble, circuit_norm, bytes, doubles, seenBytes]
  tables_channels := by
    intro table h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [circuit_norm, seenReader]
    · exact List.Subset.trans ((ensemble (p := p)).tables_channels table h)
        (List.subset_cons_self _ _)
  verifier := forwardingVerifier
  verifier_channels := by simp [ensemble, circuit_norm, forwardingVerifier, bytes, seenBytes]

/-- The stages: `seenBytes` after `doubles` after `bytes`, each a whole channel. -/
abbrev stages : List (Stage (F p)) :=
  { channel := seenBytes.toRaw } :: finished.map fun channel => { channel }

/-- Sound under `Balance.logUpUpTo 255`. The reader's spec comes from the verifier's push to
`seenBytes`, which is paid for by the verifier's pull from `bytes`, finished earlier. -/
theorem tableSoundness_withForwardingVerifier :
    (ensembleWithForwardingVerifier (p := p)).TableSoundness (Balance.logUpUpTo 255) := by
  apply Ensemble.tableSoundness_of_stagedRequirementsOn (ens := ensembleWithForwardingVerifier)
    stages
  · simp [ensembleWithForwardingVerifier, ensemble]
  · intro table h c h_c _ _ _
    simp only [ensembleWithForwardingVerifier, List.mem_cons] at h
    rcases h with h | h
    · rw [h] at h_c
      simp [circuit_norm, seenReader] at h_c
      subst h_c
      exact ⟨{ channel := seenBytes.toRaw }, List.mem_cons_self, rfl, rfl⟩
    · exact ⟨{ channel := c }, List.mem_cons_of_mem _
        (List.mem_map_of_mem (guarantees_subset_finished _ h h_c)), rfl, rfl⟩
  · intro c h_c _ _ _ _
    simp [ensembleWithForwardingVerifier, circuit_norm, forwardingVerifier, bytes] at h_c
    subst h_c
    exact ⟨{ channel := bytes.channel.toRaw }, List.mem_cons_of_mem _
      (List.mem_map_of_mem (by simp [finished])), rfl, rfl⟩
  · simp only [stages, finished, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro component h
    simp only [ensembleWithForwardingVerifier, List.mem_cons] at h
    rcases h with rfl | h
    · -- the reader owes nothing anywhere: its one pull has multiplicity `1`
      simp only [stages, finished, List.map_cons, List.map_nil, circuit_norm]
      refine ⟨?_, ?_, ?_⟩ <;> exact Component.requirementsAfterOn_of_not_mem _
        (by simp [circuit_norm, seenReader])
    refine ⟨Component.requirementsAfterOn_of_not_mem _ ?_,
      Component.stagedRequirementsOn_of_stagedRequirements (stagedRequirements component h)⟩
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · simp [circuit_norm, consumer, seenBytes_ne_doubles]
    · simp [circuit_norm, doubler, seenBytes_ne_doubles]
    · simp [circuit_norm, seenBytes_ne_bytes]
  · refine ⟨?_, Ensemble.verifierStagedRequirementsOn_of_not_mem ?_⟩
    · intro data h_earlier i h_i _
      have h_bytes := h_earlier { channel := bytes.channel.toRaw } (by simp [finished])
      simp [Ensemble.VerifierGuaranteesOn, ensembleWithForwardingVerifier, circuit_norm,
        forwardingVerifier, bytes, seenBytes, Operations.interactionValuesWith_eq_map]
        at h_bytes h_i ⊢
      subst h_i
      rw [AbstractInteraction.eval_guarantees, ChannelInteraction.toRaw_guarantees] at h_bytes
      rw [AbstractInteraction.eval_requirements, ChannelInteraction.toRaw_requirements]
      simp_all [circuit_norm, ChannelInteraction.Guarantees, ChannelInteraction.Requirements,
        bytes]
    · simp [ensembleWithForwardingVerifier, circuit_norm, forwardingVerifier,
        Ne.symm seenBytes_ne_doubles, Ne.symm seenBytes_ne_bytes]

end RangeCheckedCount
