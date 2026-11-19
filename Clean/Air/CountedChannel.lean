module

public import Clean.Air.Balance
public import Clean.Circuit.Explicit

@[expose] public section

/-!
# Channels with counted pulls

A table that answers `k` identical lookups with one row pulls the fact it relies on once, with
multiplicity `k`. `Channel.counted N channel` is `channel` with pulls of multiplicity up to `N`:
such a pull gets the guarantee, and an active push owes it. It is `RawChannel.ConsistentUpTo N`,
so it can be finished in a `SoundEnsemble` whose balance check has a `pullBound` of at least `N`,
such as `Balance.logUpUpTo N`: at exactly `N` by instance, above it through
`counted_consistentUpTo_of_le`.
-/

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

omit [FiniteField F] in
/-- Channels with different names are different. Lets `circuit_norm` tell a counted channel apart
from the other channels of a circuit without unfolding them. -/
@[circuit_norm] lemma RawChannel.eq_false_of_name_ne {a b : RawChannel F}
    (h : a.name ≠ b.name) : (a = b) = False :=
  eq_false fun h_eq => h (congrArg RawChannel.name h_eq)

namespace Channel

/-- `channel`, with pulls of multiplicity up to `N`.

It keeps `channel.name`, so `channel.toRaw` and `channel.counted N` for each `N` may be different
`RawChannel`s under one name. An ensemble uses only one of them, since its channel names are unique
(`unique_channel_names`, and `fresh` in `SoundEnsemble.addChannel`). The name is kept for witness
generation, which tallies interactions by name, and whose `DemandMode` and `PreallocatedMode` take
the typed `Channel`: under a new name, no component would answer the counted interactions, and
generation would fail with `unhandledImbalance`. -/
def counted (N : ℕ) (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    CountUpTo N mult → channel.Guarantees (fromElements message) data
  Requirements direction mult message data :=
    match direction with
    | .push => mult ≠ 0 → channel.Guarantees (fromElements message) data
    | .pull => mult = 0 ∨ CountUpTo N mult

@[circuit_norm] lemma counted_name (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).name = channel.name := rfl
@[circuit_norm] lemma counted_arity (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).arity = size Message := rfl

/-- `counted 1` guarantees what `channel.toRaw` does: only at multiplicity `1`. -/
lemma counted_one_guarantees_iff (channel : Channel F Message) (mult : F)
    (message : Vector F (size Message)) (data : ProverData F) :
    (channel.counted 1).Guarantees mult message data ↔
      channel.toRaw.Guarantees mult message data := by
  simp [counted, toRaw, countUpTo_one_iff]

/-- `counted 1` requires what `channel.toRaw` does: an active push owes the guarantee, and a pull
has multiplicity `0` or `1`. -/
lemma counted_one_requirements_iff (channel : Channel F Message) (direction : Direction) (mult : F)
    (message : Vector F (size Message)) (data : ProverData F) :
    (channel.counted 1).Requirements direction mult message data ↔
      channel.toRaw.Requirements direction mult message data := by
  cases direction <;> simp [counted, toRaw, countUpTo_one_iff]

/-- The interaction of pulling `msg` `count` times from `channel.counted N`. -/
def pulledUpTo (N : ℕ) (channel : Channel F Message) (count : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨ channel.counted N, .pull, count, toElements msg ⟩

/-- The interaction of pushing `msg` `mult` times to `channel.counted N`. -/
def emittedUpTo (N : ℕ) (channel : Channel F Message) (mult : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨ channel.counted N, .push, mult, toElements msg ⟩

/-- Pull `msg` `count` times from `channel.counted N`, which requires `count` to be `0` or to count
up to `N`. -/
@[circuit_norm]
def pullUpTo (N : ℕ) (channel : Channel F Message) (count : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (pulledUpTo N channel count msg)])

/-- Push `msg` `mult` times to `channel.counted N`. -/
@[circuit_norm]
def emitUpTo (N : ℕ) (channel : Channel F Message) (mult : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (emittedUpTo N channel mult msg)])

instance {N : ℕ} {channel : Channel F Message} {count : Expression F} :
    ExplicitCircuits (F := F) (channel.pullUpTo N count) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (pulledUpTo N channel count msg)]
  channelsWithGuarantees _ _ := [channel.counted N]

instance {N : ℕ} {channel : Channel F Message} {mult : Expression F} :
    ExplicitCircuits (F := F) (channel.emitUpTo N mult) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (emittedUpTo N channel mult msg)]
  channelsWithGuarantees _ _ := []

attribute [explicit_circuit_no_unfold] pullUpTo emitUpTo

section
variable {N : ℕ} {channel : Channel F Message} {mult : Expression F}
  {msg : Message (Expression F)} {env : Environment F}

@[circuit_norm] lemma pulledUpTo_channel :
    (pulledUpTo N channel mult msg).channel = channel.counted N := rfl
@[circuit_norm] lemma pulledUpTo_direction :
    (pulledUpTo N channel mult msg).direction = .pull := rfl
@[circuit_norm] lemma pulledUpTo_mult :
    (pulledUpTo N channel mult msg).mult = mult := rfl
@[circuit_norm] lemma pulledUpTo_msg :
    (pulledUpTo N channel mult msg).msg = toElements msg := rfl
@[circuit_norm] lemma emittedUpTo_channel :
    (emittedUpTo N channel mult msg).channel = channel.counted N := rfl
@[circuit_norm] lemma emittedUpTo_direction :
    (emittedUpTo N channel mult msg).direction = .push := rfl
@[circuit_norm] lemma emittedUpTo_mult :
    (emittedUpTo N channel mult msg).mult = mult := rfl
@[circuit_norm] lemma emittedUpTo_msg :
    (emittedUpTo N channel mult msg).msg = toElements msg := rfl

@[circuit_norm] lemma pulledUpTo_guarantees :
    (pulledUpTo N channel mult msg).Guarantees env ↔
      (CountUpTo N (Expression.eval env mult) → channel.Guarantees (eval env msg) env.data) := by
  simp [pulledUpTo, AbstractInteraction.Guarantees, counted,
    ProvableType.fromElements_toElements]

@[circuit_norm] lemma pulledUpTo_requirements :
    (pulledUpTo N channel mult msg).Requirements env ↔
      (Expression.eval env mult = 0 ∨ CountUpTo N (Expression.eval env mult)) := by
  simp [pulledUpTo, AbstractInteraction.Requirements, counted]

@[circuit_norm] lemma emittedUpTo_guarantees :
    (emittedUpTo N channel mult msg).Guarantees env := by
  simp [emittedUpTo, AbstractInteraction.Guarantees]

@[circuit_norm] lemma emittedUpTo_requirements :
    (emittedUpTo N channel mult msg).Requirements env ↔
      (Expression.eval env mult ≠ 0 → channel.Guarantees (eval env msg) env.data) := by
  simp [emittedUpTo, AbstractInteraction.Requirements, counted,
    ProvableType.fromElements_toElements]
end

/-- A pull of multiplicity up to `N` is matched by a push, whose requirement gives the
guarantee. Every other interaction's guarantee is vacuous. -/
instance (N : ℕ) (channel : Channel F Message) : (channel.counted N).ConsistentUpTo N where
  consistent interactions data balanced reqs a a_mem := by
    obtain ⟨ a_channel, - ⟩ := reqs a a_mem
    by_cases a_pull : a.PullUpTo N
    case neg =>
      rcases a with ⟨ _, a_direction, a_mult, a_msg, a_size ⟩
      subst a_channel
      simp only [Interaction.Guarantees, counted]
      exact fun h_direction h_count => absurd ⟨ h_direction, h_count ⟩ a_pull
    obtain ⟨ b, b_mem, b_msg, b_ne_zero, b_not_pull ⟩ := balanced.matchedUpTo a a_mem a_pull
    obtain ⟨ b_channel, b_reqs ⟩ := reqs b b_mem
    rcases a with ⟨ _, a_direction, a_mult, a_msg, a_size ⟩
    rcases b with ⟨ _, b_direction, b_mult, b_msg', b_size ⟩
    subst a_channel b_channel
    simp only at b_msg
    subst b_msg
    simp only [Interaction.Guarantees, Interaction.Requirements, Interaction.msgVector,
      counted] at b_reqs ⊢
    intro _ _
    cases b_direction with
    | push => exact b_reqs b_ne_zero
    | pull => exact absurd (b_reqs.resolve_left b_ne_zero) (b_not_pull rfl)

/-- Instance search sees `(Balance.logUpUpTo N).pullBound` as `N`, which
`SoundEnsemble.markFinished` relies on. -/
example [ComputableRingChar F] (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).ConsistentUpTo (Balance.logUpUpTo (F := F) N).pullBound :=
  inferInstance

/-- `channel.counted N` is also `ConsistentUpTo M` for `N ≤ M`.

Not an instance, since synthesis would have to prove `N ≤ M`. To finish `channel.counted N` under a
check whose `pullBound` is a larger `M`, provide this with `haveI` before
`SoundEnsemble.markFinished`, or pass it explicitly with `@`. -/
theorem counted_consistentUpTo_of_le {M N : ℕ} (h : N ≤ M) (channel : Channel F Message) :
    (channel.counted N).ConsistentUpTo M where
  consistent interactions data balanced :=
    RawChannel.ConsistentUpTo.consistent (N := N) interactions data
      ⟨ balanced.toBalancedInteractions, balanced.matchedUpTo.mono h ⟩

/--
For `2 ≤ N < ringChar F`, and a message `m` that `channel` does not guarantee, `channel.counted N`
is not `RawChannel.Consistent`: it needs the premise `BalancedUpTo N` of `ConsistentUpTo N`.

Two pulls of `m`, of multiplicities `N` and `1`, satisfy `BalancedInteractions`. Since `N` is
neither `0` nor `1` in `F`, `exists_push_of_pull` takes the pull of `N` as an `Interaction.Push`
matching the pull of `1`, and the count condition does not apply to `m`. The counted channel reads
both as pulls, so consistency would give the pull of `1` the guarantee of `m`.
-/
theorem counted_not_consistent {N : ℕ} (hN : 2 ≤ N) (h_char : N < ringChar F)
    (channel : Channel F Message) (m : Message F) (data : ProverData F)
    (h_m : ¬ channel.Guarantees m data) : ¬ (channel.counted N).Consistent := by
  rintro ⟨ consistent ⟩
  have cast_inj {a b : ℕ} (ha : a < ringChar F) (hb : b < ringChar F) :
      (a : F) = (b : F) → a = b :=
    fun h => (Lean.Grind.IsCharP.natCast_eq_iff_of_lt (α := F) _ ha hb).mp h
  have hN0 : (N : F) ≠ 0 := fun h => by
    have := cast_inj h_char (b := 0) (by omega) (by simpa using h); omega
  have hN1 : (N : F) ≠ 1 := fun h => by
    have := cast_inj h_char (b := 1) (by omega) (by simpa using h); omega
  let mk : F → Interaction F :=
    fun mult => ⟨ channel.counted N, .pull, mult, (toElements m).toArray, by simp [counted] ⟩
  let l := [mk (N : F), mk 1]
  have h_bal : BalancedInteractions l := by
    constructor
    · -- the pull of `1` is matched by the pull of `N`, which `Interaction.Push` counts as a push
      intro a a_mem _
      refine ⟨ mk (N : F), by simp [l], ?_, hN0, fun _ => hN1 ⟩
      simp only [l, List.mem_cons, List.not_mem_nil, or_false] at a_mem
      rcases a_mem with rfl | rfl <;> rfl
    · -- the multiplicity `N` is neither `0` nor `1`, so only untouched messages qualify
      intro msg is_bool
      by_cases h_msg : (toElements m).toArray = msg
      · exfalso
        rcases is_bool (mk (N : F)) (by simp [l]) h_msg with h | h
        · exact hN0 h
        · exact hN1 h
      · simp [activeCount, l, mk, h_msg]
  have h_reqs : ∀ i ∈ l, i.channel = channel.counted N ∧ i.Requirements data := by
    intro i h_i
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at h_i
    rcases h_i with rfl | rfl
    · refine ⟨ rfl, ?_ ⟩
      simp only [Interaction.Requirements, mk, counted, Interaction.msgVector]
      exact .inr ⟨ N, by omega, le_rfl, rfl ⟩
    · refine ⟨ rfl, ?_ ⟩
      simp only [Interaction.Requirements, mk, counted, Interaction.msgVector]
      exact .inr ⟨ 1, le_rfl, by omega, by simp ⟩
  have h_g := consistent l data h_bal h_reqs (mk 1) (by simp [l])
  simp only [Interaction.Guarantees, mk, counted, Interaction.msgVector] at h_g
  apply h_m
  have h := h_g trivial ⟨ 1, le_rfl, by omega, by simp ⟩
  convert h
  simp [ProvableType.fromElements_toElements]

end Channel
