module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Soundness by channel finishing order

`OrderedChannel` orders tables, so no table may both pull from a channel and owe requirements on
it. This file orders channels instead: a table may do both, as long as its requirements on the
channel follow from its guarantees on channels finished earlier. An example is a table that
range-checks the multiplicity of a counted pull with a lookup on another channel
(`Clean/Examples/RangeCheckedCount.lean`).

`finished` lists the channels newest first, and `Component.StagedRequirements` asks a component's
requirements on each to follow from its guarantees on the channels after it in the list. By
induction from the oldest channel, each finished channel's requirements hold, hence by consistency
its guarantees, hence every table's spec (`Ensemble.tableSoundness_of_stagedRequirements`). Stages,
in the second half, refine a channel into classes of its messages.

The verifier takes part in each stage like a table: the stage's consistency gives its pulls their
guarantees, from which its spec follows, and its requirements on a stage are a hypothesis that may
use its guarantees on earlier stages (`Ensemble.VerifierStagedRequirementsOn`).

Not covered: there is no staged counterpart of `Ensemble.addVm_soundVmChannel_of_soundChannels` for
adding a VM.
-/

variable {F : Type} [FiniteField F]

namespace Air.Flat

/-- The requirements of `table` on `channel` follow from its assumptions, its constraints and its
guarantees on `earlier` channels. -/
def Table.RequirementsAfter (table : Table F) (channel : RawChannel F)
    (earlier : List (RawChannel F)) : Prop :=
  table.Assumptions → table.Constraints → (∀ c ∈ earlier, table.ChannelGuarantees c) →
    table.ChannelRequirements channel

/-- `Table.RequirementsAfter` for every table of the component. -/
def Component.RequirementsAfter (component : Component F) (channel : RawChannel F)
    (earlier : List (RawChannel F)) : Prop :=
  ∀ table : Table F, table.component = component → table.RequirementsAfter channel earlier

/-- `RequirementsAfter` on each channel of a finishing order listed newest first, with the channels
after it in the list as `earlier`. -/
def Component.StagedRequirements (component : Component F) : List (RawChannel F) → Prop
  | [] => True
  | channel :: earlier =>
    component.RequirementsAfter channel earlier ∧ component.StagedRequirements earlier

@[circuit_norm] lemma Component.stagedRequirements_nil (component : Component F) :
    component.StagedRequirements [] := trivial

@[circuit_norm] lemma Component.stagedRequirements_cons (component : Component F)
    (channel : RawChannel F) (earlier : List (RawChannel F)) :
    component.StagedRequirements (channel :: earlier) ↔
      component.RequirementsAfter channel earlier ∧ component.StagedRequirements earlier :=
  .rfl

/-- A component owes nothing on a channel outside its `channelsWithRequirements`. -/
lemma Component.requirementsAfter_of_not_mem {component : Component F} {channel : RawChannel F}
    (earlier : List (RawChannel F))
    (h : channel ∉ component.circuit.channelsWithRequirements) :
    component.RequirementsAfter channel earlier := by
  rintro table rfl - constraints -
  exact table.requirements_of_not_mem_of_constraints constraints h

/-- A component whose guarantees all come from earlier channels gets its requirements from
soundness. -/
lemma Component.requirementsAfter_of_guarantees_subset {component : Component F}
    {channel : RawChannel F} {earlier : List (RawChannel F)}
    (h : component.circuit.channelsWithGuarantees ⊆ earlier) :
    component.RequirementsAfter channel earlier := by
  rintro table rfl assumptions constraints guarantees
  have all_guarantees : table.Guarantees := by
    rw [Table.guarantees_iff_channelGuarantees]
    exact fun c hc => guarantees c (h hc)
  exact table.channelRequirements_of_requirements
    (Table.weakSoundness assumptions constraints all_guarantees).2

/-- `StagedRequirements` from `RequirementsAfter` at every position of the list. -/
lemma Component.stagedRequirements_of_forall {component : Component F} :
    ∀ {finished : List (RawChannel F)},
    (∀ (channel : RawChannel F) (earlier : List (RawChannel F)),
      (∃ later, later ++ channel :: earlier = finished) →
      component.RequirementsAfter channel earlier) →
    component.StagedRequirements finished
  | [], _ => trivial
  | channel :: earlier, h =>
    ⟨h channel earlier ⟨[], rfl⟩,
      Component.stagedRequirements_of_forall fun c e ⟨later, hl⟩ =>
        h c e ⟨channel :: later, by simp [hl]⟩⟩

/-!
## Stages: a channel and a class of its messages

A table that pulls some messages of a channel and pushes others is not a cycle, but a channel
order cannot finish one class before the other. For example, on the ALU bus of a zkVM outside this
repository, a division table pulls `LT` and `MUL` results and pushes `DIVREM` results. Ordering
stages instead lets the `DIVREM` stage finish after the `LT`/`MUL` stage. Balance is message by
message (`BalancedUpTo.filter_msg`), so each stage balances by itself.
-/

/-- The messages of one class on one channel. The default class is every message, so `{ channel }`
is the whole channel. -/
structure Stage (F : Type) where
  channel : RawChannel F
  cls : Array F → Bool := fun _ => true

/-- The guarantees of `table` on the interactions of a stage. -/
def Table.GuaranteesOn (table : Table F) (stage : Stage F) : Prop :=
  ∀ i ∈ table.interactionsWith stage.channel, stage.cls i.msg → i.Guarantees table.data

/-- The requirements of `table` on the interactions of a stage. -/
def Table.RequirementsOn (table : Table F) (stage : Stage F) : Prop :=
  ∀ i ∈ table.interactionsWith stage.channel, stage.cls i.msg → i.Requirements table.data

/-- `Table.RequirementsAfter` over stages. -/
def Table.RequirementsAfterOn (table : Table F) (stage : Stage F) (earlier : List (Stage F)) :
    Prop :=
  table.Assumptions → table.Constraints → (∀ s ∈ earlier, table.GuaranteesOn s) →
    table.RequirementsOn stage

/-- `Table.RequirementsAfterOn` for every table of the component. -/
def Component.RequirementsAfterOn (component : Component F) (stage : Stage F)
    (earlier : List (Stage F)) : Prop :=
  ∀ table : Table F, table.component = component → table.RequirementsAfterOn stage earlier

/-- `Component.StagedRequirements` over stages, newest first. -/
def Component.StagedRequirementsOn (component : Component F) : List (Stage F) → Prop
  | [] => True
  | stage :: earlier =>
    component.RequirementsAfterOn stage earlier ∧ component.StagedRequirementsOn earlier

@[circuit_norm] lemma Component.stagedRequirementsOn_nil (component : Component F) :
    component.StagedRequirementsOn [] := trivial

@[circuit_norm] lemma Component.stagedRequirementsOn_cons (component : Component F)
    (stage : Stage F) (earlier : List (Stage F)) :
    component.StagedRequirementsOn (stage :: earlier) ↔
      component.RequirementsAfterOn stage earlier ∧ component.StagedRequirementsOn earlier :=
  .rfl

/-- Guarantees on stages that cover every pull of a table give all its guarantees. -/
lemma Table.guarantees_of_guaranteesOn {table : Table F} {stages : List (Stage F)}
    (covered : ∀ c ∈ table.component.circuit.channelsWithGuarantees,
      ∀ i ∈ table.interactionsWith c, i.direction = .pull →
        ∃ s ∈ stages, s.channel = c ∧ s.cls i.msg)
    (guarantees : ∀ s ∈ stages, table.GuaranteesOn s) : table.Guarantees := by
  rw [Table.guarantees_iff_channelGuarantees]
  intro c h_c
  rw [Table.channelGuarantees_iff_forall]
  intro i h_i
  by_cases h_pull : i.direction = .pull
  · obtain ⟨ s, h_s, rfl, h_cls ⟩ := covered c h_c i h_i h_pull
    exact guarantees s h_s i h_i h_cls
  · exact fun h => absurd h h_pull

/-- A component owes nothing on a stage whose channel is outside its `channelsWithRequirements`. -/
lemma Component.requirementsAfterOn_of_not_mem {component : Component F} {stage : Stage F}
    (earlier : List (Stage F))
    (h : stage.channel ∉ component.circuit.channelsWithRequirements) :
    component.RequirementsAfterOn stage earlier := by
  rintro table rfl - constraints - i h_i -
  have := table.requirements_of_not_mem_of_constraints constraints h
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

/-- A component whose pulls all lie in earlier stages gets its requirements from soundness. -/
lemma Component.requirementsAfterOn_of_covered {component : Component F} {stage : Stage F}
    {earlier : List (Stage F)}
    (covered : ∀ table : Table F, table.component = component →
      ∀ c ∈ component.circuit.channelsWithGuarantees,
      ∀ i ∈ table.interactionsWith c, i.direction = .pull →
        ∃ s ∈ earlier, s.channel = c ∧ s.cls i.msg) :
    component.RequirementsAfterOn stage earlier := by
  rintro table rfl assumptions constraints guarantees i h_i -
  have all_guarantees := Table.guarantees_of_guaranteesOn (covered table rfl) guarantees
  have := table.channelRequirements_of_requirements (channel := stage.channel)
    (Table.weakSoundness assumptions constraints all_guarantees).2
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

/-- The same, when every message of each guarantee channel lies in an earlier stage. -/
lemma Component.requirementsAfterOn_of_guarantees_subset {component : Component F}
    {stage : Stage F} {earlier : List (Stage F)}
    (h : ∀ c ∈ component.circuit.channelsWithGuarantees, ∀ msg,
      ∃ s ∈ earlier, s.channel = c ∧ s.cls msg) :
    component.RequirementsAfterOn stage earlier :=
  Component.requirementsAfterOn_of_covered fun _ _ c h_c i _ _ => h c h_c i.msg

/-- A channel-level `RequirementsAfter` gives the stage-level one for the whole channel, when each
of `earlierChannels` is the channel of a whole-channel stage in `earlier`. -/
lemma Component.requirementsAfterOn_of_requirementsAfter {component : Component F}
    {channel : RawChannel F} {earlierChannels : List (RawChannel F)} {earlier : List (Stage F)}
    (h : component.RequirementsAfter channel earlierChannels)
    (h_earlier : ∀ c ∈ earlierChannels, ∃ s ∈ earlier, s.channel = c ∧ ∀ msg, s.cls msg) :
    component.RequirementsAfterOn { channel } earlier := by
  rintro table h_comp assumptions constraints guarantees i h_i -
  have := h table h_comp assumptions constraints (fun c hc => by
    obtain ⟨s, hs, rfl, hall⟩ := h_earlier c hc
    rw [Table.channelGuarantees_iff_forall]
    exact fun i hi => guarantees s hs i hi (hall _))
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

/-- `StagedRequirements` on channels is `StagedRequirementsOn` on their whole-channel stages. -/
lemma Component.stagedRequirementsOn_of_stagedRequirements {component : Component F} :
    ∀ {finished : List (RawChannel F)}, component.StagedRequirements finished →
      component.StagedRequirementsOn (finished.map fun channel => { channel })
  | [], _ => trivial
  | _ :: _, ⟨after, rest⟩ =>
    ⟨ Component.requirementsAfterOn_of_requirementsAfter after
        fun c hc => ⟨{ channel := c }, List.mem_map_of_mem hc, rfl, fun _ => rfl⟩,
      Component.stagedRequirementsOn_of_stagedRequirements rest ⟩

namespace Ensemble
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-!
### The verifier on a stage

The verifier interacts with channels too, so a stage's interactions are the tables' and the
verifier's. Its pulls have unconditional requirements (`Verifier.Operation.interact`); its pushes
owe the channel's guarantee for a message computed from the public input, which nothing proves in
general. So the verifier's requirements on a stage are a hypothesis, which, like a component's, may
use its guarantees on earlier stages. In the common case the verifier pushes nothing on the
stage's channel, and `verifierRequirementsAfterOn_of_not_mem` discharges it.
-/

/-- The verifier's guarantees on the interactions of a stage. -/
def VerifierGuaranteesOn (ens : Ensemble F PublicIO) (data : ProverData F) (stage : Stage F) :
    Prop :=
  ∀ i ∈ ens.verifierOperations.interactionValuesWith stage.channel data.publicEnvironment,
    stage.cls i.msg → i.Guarantees data

/-- The verifier's requirements on the interactions of a stage. -/
def VerifierRequirementsOn (ens : Ensemble F PublicIO) (data : ProverData F) (stage : Stage F) :
    Prop :=
  ∀ i ∈ ens.verifierOperations.interactionValuesWith stage.channel data.publicEnvironment,
    stage.cls i.msg → i.Requirements data

/-- The verifier's requirements on a stage follow from its guarantees on `earlier` stages. -/
def VerifierRequirementsAfterOn (ens : Ensemble F PublicIO) (stage : Stage F)
    (earlier : List (Stage F)) : Prop :=
  ∀ data : ProverData F, (∀ s ∈ earlier, ens.VerifierGuaranteesOn data s) →
    ens.VerifierRequirementsOn data stage

/-- `Component.StagedRequirementsOn` for the verifier. -/
def VerifierStagedRequirementsOn (ens : Ensemble F PublicIO) : List (Stage F) → Prop
  | [] => True
  | stage :: earlier =>
    ens.VerifierRequirementsAfterOn stage earlier ∧ ens.VerifierStagedRequirementsOn earlier

@[circuit_norm] lemma verifierStagedRequirementsOn_nil (ens : Ensemble F PublicIO) :
    ens.VerifierStagedRequirementsOn [] := trivial

@[circuit_norm] lemma verifierStagedRequirementsOn_cons (ens : Ensemble F PublicIO)
    (stage : Stage F) (earlier : List (Stage F)) :
    ens.VerifierStagedRequirementsOn (stage :: earlier) ↔
      ens.VerifierRequirementsAfterOn stage earlier ∧ ens.VerifierStagedRequirementsOn earlier :=
  .rfl

/-- The verifier owes nothing on a stage whose channel it pushes nothing to. -/
lemma verifierRequirementsAfterOn_of_not_mem {ens : Ensemble F PublicIO} {stage : Stage F}
    (earlier : List (Stage F))
    (h : stage.channel ∉ ens.verifier.channelsWithRequirements) :
    ens.VerifierRequirementsAfterOn stage earlier := by
  intro data _ i h_i _
  have := ens.verifierChannelRequirements_of_not_mem data h
  rw [Ensemble.VerifierChannelRequirements, Operations.ChannelRequirements,
    ← Operations.forall_interactionsWith_iff] at this
  rw [Operations.interactionValuesWith_eq_map] at h_i
  obtain ⟨i', h_i', rfl⟩ := List.mem_map.mp h_i
  exact this i' h_i'

/-- The verifier owes nothing on stages whose channels it pushes nothing to. -/
lemma verifierStagedRequirementsOn_of_not_mem {ens : Ensemble F PublicIO} :
    ∀ {finished : List (Stage F)},
    (∀ s ∈ finished, s.channel ∉ ens.verifier.channelsWithRequirements) →
      ens.VerifierStagedRequirementsOn finished
  | [], _ => trivial
  | _ :: _, h =>
    ⟨ verifierRequirementsAfterOn_of_not_mem _ (h _ List.mem_cons_self),
      verifierStagedRequirementsOn_of_not_mem fun s hs => h s (List.mem_cons_of_mem _ hs) ⟩

/-- An empty verifier owes nothing on any stage. -/
lemma verifierStagedRequirementsOn_of_verifier_empty {ens : Ensemble F PublicIO}
    (h : ens.verifier = .empty F PublicIO) (finished : List (Stage F)) :
    ens.VerifierStagedRequirementsOn finished :=
  verifierStagedRequirementsOn_of_not_mem fun _ _ => by
    simp [h, circuit_norm, Verifier.Program.empty]

/-- Every table's and the verifier's guarantees on each finished stage hold, by induction from the
oldest stage. -/
theorem guaranteesOn_of_stagedRequirementsOn {ens : Ensemble F PublicIO} {N : ℕ}
    (witness : EnsembleWitness ens) (assumptions : witness.Assumptions)
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels N) :
    ∀ {finished : List (Stage F)}, (∀ s ∈ finished, s.channel ∈ ens.channels) →
    (∀ s ∈ finished, s.channel.ConsistentUpTo N) →
    (∀ component ∈ ens.tables, component.StagedRequirementsOn finished) →
    ens.VerifierStagedRequirementsOn finished →
    (∀ table ∈ witness.tables, ∀ s ∈ finished, table.GuaranteesOn s) ∧
      ∀ s ∈ finished, ens.VerifierGuaranteesOn witness.data s
  | [], _, _, _, _ => by simp
  | stage :: earlier, finished_channels, consistent, staged, verifier_staged => by
    have ih := guaranteesOn_of_stagedRequirementsOn witness assumptions
      constraints balanced (fun s hs => finished_channels s (List.mem_cons_of_mem _ hs))
      (fun s hs => consistent s (List.mem_cons_of_mem _ hs))
      (fun component h => (staged component h).2) verifier_staged.2
    have requirements : ∀ table ∈ witness.tables, table.RequirementsOn stage :=
      fun table h_table =>
        (staged table.component (witness.component_mem_tables_of_mem h_table)).1 table rfl
          (assumptions table h_table) (constraints table h_table) (ih.1 table h_table)
    have verifier_requirements : ens.VerifierRequirementsOn witness.data stage :=
      verifier_staged.1 witness.data ih.2
    -- the stage's interactions balance by themselves, satisfy their requirements, and so by
    -- consistency their guarantees
    have : stage.channel.ConsistentUpTo N := consistent stage List.mem_cons_self
    have all_guarantees := RawChannel.ConsistentUpTo.consistent
      ((witness.interactionsWith stage.channel).filter fun i => stage.cls i.msg) witness.data
      ((balanced stage.channel (finished_channels stage List.mem_cons_self)).filter_msg _)
      (by
        intro i h_i
        obtain ⟨h_i, h_cls⟩ := List.mem_filter.mp h_i
        refine ⟨witness.channel_eq_of_mem_interactionsWith h_i, ?_⟩
        rcases witness.mem_interactionsWith.mp h_i with h_i | ⟨table, h_table, h_i⟩
        · exact verifier_requirements i h_i h_cls
        · have := requirements table h_table i h_i h_cls
          rwa [witness.same_data table h_table] at this)
    have mem_stage : ∀ i, i ∈ witness.interactionsWith stage.channel → stage.cls i.msg →
        i ∈ (witness.interactionsWith stage.channel).filter fun i => stage.cls i.msg :=
      fun i h_i h_cls => List.mem_filter.mpr ⟨h_i, h_cls⟩
    refine ⟨fun table h_table s h_s => ?_, fun s h_s => ?_⟩
    · rcases List.mem_cons.mp h_s with rfl | h_s
      · intro i h_i h_cls
        rw [witness.same_data table h_table]
        exact all_guarantees i (mem_stage i
          (witness.mem_interactionsWith.mpr (.inr ⟨table, h_table, h_i⟩)) h_cls)
      · exact ih.1 table h_table s h_s
    · rcases List.mem_cons.mp h_s with rfl | h_s
      · intro i h_i h_cls
        exact all_guarantees i (mem_stage i (witness.mem_interactionsWith.mpr (.inl h_i)) h_cls)
      · exact ih.2 s h_s

/--
`tableSoundness_of_stagedRequirements` over stages. Every pull of a table, and of the verifier, on a
channel with guarantees lies in a finished stage; each finished stage's channel is consistent; and
the requirements of every component and of the verifier on a stage follow from their guarantees on
the stages finished before it.
-/
theorem tableSoundness_of_stagedRequirementsOn {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (Stage F))
    (finished_channels : ∀ s ∈ finished, s.channel ∈ ens.channels)
    (covered : ∀ table : Table F, table.component ∈ ens.tables →
      ∀ c ∈ table.component.circuit.channelsWithGuarantees,
      ∀ i ∈ table.interactionsWith c, i.direction = .pull →
        ∃ s ∈ finished, s.channel = c ∧ s.cls i.msg)
    (verifier_covered : ∀ c ∈ ens.verifier.channelsWithGuarantees, ∀ data : ProverData F,
      ∀ i ∈ ens.verifierOperations.interactionValuesWith c data.publicEnvironment,
        i.direction = .pull → ∃ s ∈ finished, s.channel = c ∧ s.cls i.msg)
    (consistent : ∀ s ∈ finished, s.channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirementsOn finished)
    (verifier_staged : ens.VerifierStagedRequirementsOn finished) :
    ens.TableSoundness balance := by
  intro witness assumptions constraints fit balanced
  have guarantees := guaranteesOn_of_stagedRequirementsOn witness assumptions
    constraints (witness.balancedChannels_of_balanced fit balanced)
    finished_channels consistent staged verifier_staged
  refine ⟨?_, fun table h_table => ?_⟩
  · apply ens.verifierSpec_of_verifierGuarantees
    rw [verifierGuarantees_iff]
    intro c h_c
    rw [witness.verifierChannelGuarantees_iff_forall]
    intro i h_i
    by_cases h_pull : i.direction = .pull
    · obtain ⟨s, h_s, rfl, h_cls⟩ := verifier_covered _ h_c witness.data i h_i h_pull
      exact guarantees.2 s h_s i h_i h_cls
    · exact fun h => absurd h h_pull
  · have h_comp := witness.component_mem_tables_of_mem h_table
    have all_guarantees : table.Guarantees :=
      Table.guarantees_of_guaranteesOn (covered table h_comp) (guarantees.1 table h_table)
    exact (Table.weakSoundness (assumptions table h_table) (constraints table h_table)
      all_guarantees).1

/--
Table soundness from a finishing order of channels: every channel a table or the verifier has
guarantees on is finished, every finished channel is consistent under the balance check, and the
requirements of every component and of the verifier on a finished channel follow from their
guarantees on the channels finished before it. This is `tableSoundness_of_stagedRequirementsOn`
with each channel as a whole-channel stage. A verifier that pushes to no finished channel owes
nothing (`verifierStagedRequirementsOn_of_not_mem`), and an empty one in particular
(`verifierStagedRequirementsOn_of_verifier_empty`).
-/
theorem tableSoundness_of_stagedRequirements {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (RawChannel F))
    (finished_subset : finished ⊆ ens.channels)
    (subset_finished : ∀ component ∈ ens.tables,
      component.circuit.channelsWithGuarantees ⊆ finished)
    (verifier_subset_finished : ens.verifier.channelsWithGuarantees ⊆ finished)
    (consistent : ∀ channel ∈ finished, channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirements finished)
    (verifier_staged : ens.VerifierStagedRequirementsOn (finished.map fun channel => { channel })) :
    ens.TableSoundness balance :=
  tableSoundness_of_stagedRequirementsOn (finished.map fun channel => { channel })
    (by simpa using fun _ h => finished_subset h)
    (fun table h c h_c _ _ _ => ⟨{ channel := c },
      List.mem_map_of_mem (subset_finished table.component h h_c), rfl, rfl⟩)
    (fun c h_c _ _ _ _ => ⟨{ channel := c }, List.mem_map_of_mem (verifier_subset_finished h_c),
      rfl, rfl⟩)
    (by simpa using consistent)
    (fun component h => Component.stagedRequirementsOn_of_stagedRequirements (staged component h))
    verifier_staged

end Ensemble
end Air.Flat
