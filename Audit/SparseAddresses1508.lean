import Definitions.Def_BlottoFPTAS_Main_BitRAM

/-! # Paper 1508, Theorem 5.1

The finite-bit RAM counts the rational in each occupied memory cell. Varying the
addresses while keeping every stored value equal to one gives many states with
the same space charge.
-/

namespace Audit.SparseAddresses1508

open BlottoFPTAS.Main

private abbrev Blocks (k : ℕ) := Fin k → Fin (2 ^ k)

private def address {k : ℕ} (i : Fin k) (block : Fin (2 ^ k)) : ℤ :=
  Nat.pair i.val block.val

private theorem address_eq {k : ℕ} {i j : Fin k} {x y : Fin (2 ^ k)} :
    address i x = address j y ↔ i = j ∧ x = y := by
  simp [address, Nat.pair_eq_pair, Fin.ext_iff]

private def addresses {k : ℕ} (u : Blocks k) : Finset ℤ :=
  Finset.univ.image fun i => address i (u i)

private theorem mem_addresses {k : ℕ} (u : Blocks k) (i : Fin k) (x : Fin (2 ^ k)) :
    address i x ∈ addresses u ↔ u i = x := by
  simp [addresses, address_eq]

private def memory {k : ℕ} (u : Blocks k) : ℤ →₀ ℚ where
  support := addresses u
  toFun a := if a ∈ addresses u then 1 else 0
  mem_support_toFun a := by by_cases h : a ∈ addresses u <;> simp [h]

private def encode {k : ℕ} (u : Blocks k) : BitRAM.State :=
  { BitRAM.initState with mem := memory u }

private theorem encode_injective (k : ℕ) : Function.Injective (encode (k := k)) := by
  intro u v h
  funext i
  have atCell := congrArg (fun s : BitRAM.State => s.mem (address i (u i))) h
  change (if address i (u i) ∈ addresses u then (1 : ℚ) else 0) =
    (if address i (u i) ∈ addresses v then 1 else 0) at atCell
  by_contra hne
  simp [mem_addresses, Ne.symm hne] at atCell

private theorem encode_space {k : ℕ} (u : Blocks k) : BitRAM.space (encode u) = 3 * k := by
  have hcard : (addresses u).card = k := by
    rw [addresses, Finset.card_image_of_injective]
    · simp
    · exact fun _ _ h => (address_eq.mp h).1
  change 0 + (∑ a ∈ addresses u, ratSize ((memory u) a)) + 0 = 3 * k
  have hsize (a) (ha : a ∈ addresses u) : ratSize ((memory u) a) = 3 := by
    change ratSize (if a ∈ addresses u then 1 else 0) = 3
    rw [if_pos ha]
    decide
  simp [Finset.sum_congr rfl hsize, hcard, Nat.mul_comm]

/-- For every block width `k`, the state-space counter charges exactly `3 * k`
bits on each of `2^(k * k)` distinct states. The registers and output are empty. -/
theorem many_states_at_same_space (k : ℕ) :
    ∃ states : Finset BitRAM.State, states.card = 2 ^ (k * k) ∧
      ∀ s ∈ states, BitRAM.space s = 3 * k := by
  let enc : Blocks k ↪ BitRAM.State := ⟨encode, encode_injective k⟩
  refine ⟨Finset.univ.map enc, ?_, ?_⟩
  · simp [Blocks, pow_mul]
  · intro s hs
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hs
    exact encode_space u

/-- Scan a finite address range. Each address is loaded as a literal, and the
next coin determines whether to leave a one there. The program depends on the
range alone. -/
private def scan (bound : ℕ) : BitRAM.Program :=
  List.ofFn fun t : Fin (3 * bound + 1) =>
    if t.val = 3 * bound then .halt
    else if t.val % 3 = 0 then .const 0 ((t.val / 3 : ℕ) : ℚ)
    else if t.val % 3 = 1 then .coin 1 else .store 0 1

private noncomputable def regs (a : ℕ) (b : ℚ) : ℕ →₀ ℚ := (Finsupp.single 0 (a : ℚ)).update 1 b

private def prefixMem {k : ℕ} (u : Blocks k) (j : ℕ) :=
  (memory u).filter (fun a : ℤ => 0 ≤ a ∧ a < (j : ℤ))

private def tape {k : ℕ} (u : Blocks k) (j : ℕ) := decide ((j : ℤ) ∈ addresses u)

private theorem mem_bit {k : ℕ} (u : Blocks k) (j : ℕ) :
    BitRAM.bitVal (tape u j) = (memory u) j := by
  change (if decide _ then _ else _) = (if _ then _ else _)
  simp

private theorem prefix_next {k : ℕ} (u : Blocks k) (j : ℕ) :
    (prefixMem u j).update j ((memory u) j) = prefixMem u (j + 1) := by
  ext x
  simp only [prefixMem, Finsupp.update_apply, Finsupp.filter_apply, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

private theorem prefix_full {k : ℕ} (u : Blocks k) :
    prefixMem u (2 ^ (2 * k)) = memory u := by
  ext x
  rw [prefixMem, Finsupp.filter_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    have hx : x ∈ addresses u := by
      by_contra hx
      simp [memory, hx] at hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply h
    refine ⟨by unfold address; positivity, ?_⟩
    unfold address
    exact_mod_cast lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq i.val (u i).val)
      (by
        rw [show 2 ^ (2 * k) = (2 ^ k) ^ 2 by rw [mul_comm, pow_mul]]
        apply Nat.pow_le_pow_left
        have hi := i.isLt
        have hk := Nat.lt_two_pow_self (n := k)
        have hu := (u i).isLt
        omega)

private noncomputable abbrev scanRun {k : ℕ} (u : Blocks k) :=
  BitRAM.run (scan (2 ^ (2 * k))) [] (tape u)

/-- Contents of the machine after storing the first `j` addresses. `pc` and
`coins` also distinguish the three instructions within a loop iteration. -/
private structure Seen {k : ℕ} (u : Blocks k) (s : BitRAM.State)
    (pc coins j a : ℕ) (b : ℚ) : Prop where
  counter : s.pc = pc
  live : s.halted = false
  flips : s.coins = coins
  registers : s.regs = regs a b
  written : s.mem = prefixMem u j
  output : s.out = []

private theorem scan_step {k : ℕ} (u : Blocks k) (t : ℕ) :
    scanRun u (t + 1) = BitRAM.step (scan (2 ^ (2 * k))) [] (tape u) (scanRun u t) :=
  Function.iterate_succ_apply' _ _ _

private theorem regs_address (a d : ℕ) (b : ℚ) : (regs a b).update 0 d = regs d b := by
  ext i
  by_cases h : i = 0 <;> by_cases h' : i = 1 <;> simp_all [regs, Finsupp.update_apply, eq_comm]

private theorem prepare {k : ℕ} {u : Blocks k} {j a : ℕ} {b : ℚ} (hj : j < 2 ^ (2 * k))
    (h : Seen u (scanRun u (3 * j)) (3 * j) j j a b) :
    Seen u (scanRun u (3 * j + 1)) (3 * j + 1) j j j b := by
  have cmd : (scan (2 ^ (2 * k)))[3 * j]? = some (.const 0 (j : ℚ)) := by
    rw [scan, List.getElem?_ofFn, dif_pos (by omega)]
    simp [show 3 * j ≠ 3 * (2 ^ (2 * k)) by omega]
  rw [scan_step]
  constructor <;> simp [BitRAM.step, h.live, h.counter, cmd, h.flips, h.registers, h.output,
    h.written, regs_address]

private theorem flip {k : ℕ} {u : Blocks k} {j : ℕ} {b : ℚ} (hj : j < 2 ^ (2 * k))
    (h : Seen u (scanRun u (3 * j + 1)) (3 * j + 1) j j j b) :
    Seen u (scanRun u (3 * j + 2)) (3 * j + 2) (j + 1) j j ((memory u) j) := by
  have cmd : (scan (2 ^ (2 * k)))[3 * j + 1]? = some (.coin 1) := by
    rw [scan, List.getElem?_ofFn, dif_pos (by omega)]
    simp [show 3 * j + 1 ≠ 3 * (2 ^ (2 * k)) by omega, Nat.mul_add_mod_self_left]
  rw [show 3 * j + 2 = (3 * j + 1) + 1 from rfl, scan_step]
  constructor <;> simp [BitRAM.step, h.live, h.counter, cmd, h.flips, h.registers, h.output,
    h.written, regs, mem_bit]

private theorem store_word {k : ℕ} {u : Blocks k} {j : ℕ} (hj : j < 2 ^ (2 * k))
    (h : Seen u (scanRun u (3 * j + 2)) (3 * j + 2) (j + 1) j j ((memory u) j)) :
    Seen u (scanRun u (3 * (j + 1))) (3 * (j + 1)) (j + 1) (j + 1) j ((memory u) j) := by
  have cmd : (scan (2 ^ (2 * k)))[3 * j + 2]? = some (.store 0 1) := by
    rw [scan, List.getElem?_ofFn, dif_pos (by omega)]
    simp [show 3 * j + 2 ≠ 3 * (2 ^ (2 * k)) by omega, Nat.mul_add_mod_self_left]
  rw [show 3 * (j + 1) = (3 * j + 2) + 1 by omega, scan_step]
  constructor <;> simp [BitRAM.step, h.live, h.counter, cmd, h.flips, h.registers, h.output,
    h.written, regs, Finsupp.update_apply, prefix_next]

private theorem boundary {k : ℕ} (u : Blocks k) (j : ℕ) (hj : j ≤ 2 ^ (2 * k)) :
    ∃ a b, a < 2 ^ (2 * k) ∧ (b = 0 ∨ b = 1) ∧
      Seen u (scanRun u (3 * j)) (3 * j) j j a b := by
  induction j with
  | zero =>
    refine ⟨0, 0, by positivity, Or.inl rfl, ?_⟩
    constructor <;> try rfl
    · change 0 = regs 0 0
      simp [regs]
    · change 0 = prefixMem u 0
      ext x
      simp [prefixMem]
  | succ j ih =>
    obtain ⟨a, b, _, _, h⟩ := ih (by omega)
    have hj' : j < 2 ^ (2 * k) := hj
    refine ⟨j, (memory u) j, hj', ?_, store_word hj' (flip hj' (prepare hj' h))⟩
    change (if _ then (1 : ℚ) else 0) = 0 ∨ _
    split <;> simp_all [memory]

private theorem partial_space {k : ℕ} (u : Blocks k) (s : BitRAM.State) (j a : ℕ) (b : ℚ)
    (ha : a < 2 ^ (2 * k)) (hb : b = 0 ∨ b = 1) (hr : s.regs = regs a b)
    (hm : s.mem = prefixMem u j) (ho : s.out = []) : BitRAM.space s ≤ 5 * k + 5 := by
  have hreg : (regs a b).sum (fun _ q => ratSize q) ≤ ratSize b + ratSize (a : ℚ) := by
    have hsub : (regs a b).support ⊆ {1, 0} :=
      (Finsupp.support_update_subset _ _).trans
        (Finset.insert_subset_insert _ Finsupp.support_single_subset)
    calc
      _ ≤ ∑ i ∈ ({1, 0} : Finset ℕ), ratSize (regs a b i) := Finset.sum_le_sum_of_subset hsub
      _ = _ := by simp [regs, Finsupp.update_apply]
  have hmem : (prefixMem u j).sum (fun _ q => ratSize q) ≤ 3 * k := by
    have htotal : (memory u).sum (fun _ q => ratSize q) = 3 * k := by
      simpa [BitRAM.space, encode, BitRAM.initState] using encode_space u
    rw [← htotal]
    unfold prefixMem Finsupp.sum
    rw [Finsupp.support_filter]
    calc
      _ = ∑ i ∈ (memory u).support.filter (fun z => 0 ≤ z ∧ z < (j : ℤ)),
            ratSize ((memory u) i) := Finset.sum_congr rfl fun i hi => by
              rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hi).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have abit : ratSize (a : ℚ) ≤ 2 * k + 2 := by
    simpa [ratSize, Nat.size_one] using Nat.add_le_add_right (Nat.size_le.mpr ha) 2
  have bbit : ratSize b ≤ 3 := by rcases hb with rfl | rfl <;> decide
  rw [BitRAM.space, hr, hm, ho]
  simp only [List.length_nil, Nat.add_zero]
  omega

private theorem before_halt {k : ℕ} (u : Blocks k) (t : ℕ) (ht : t ≤ 3 * 2 ^ (2 * k)) :
    (scanRun u t).halted = false ∧ BitRAM.space (scanRun u t) ≤ 5 * k + 5 := by
  have ok {s pc coins j a b} (h : Seen u s pc coins j a b)
      (ha : a < 2 ^ (2 * k)) (hb : b = 0 ∨ b = 1) :=
    And.intro h.live (partial_space u s j a b ha hb h.registers h.written h.output)
  let j := t / 3
  have hj : j ≤ 2 ^ (2 * k) := by dsimp [j]; omega
  obtain ⟨a, b, ha, hb, h⟩ := boundary u j hj
  have phases : t = 3 * j ∨ t = 3 * j + 1 ∨ t = 3 * j + 2 := by dsimp [j]; omega
  rcases phases with h0 | h1 | h2
  · rw [h0]
    exact ok h ha hb
  · have hj' : j < 2 ^ (2 * k) := by omega
    rw [h1]
    exact ok (prepare hj' h) hj' hb
  · have hj' : j < 2 ^ (2 * k) := by omega
    rw [h2]
    apply ok (flip hj' (prepare hj' h)) hj'
    change (if _ then (1 : ℚ) else 0) = 0 ∨ _
    split <;> simp_all [memory]

private theorem scan_finishes {k : ℕ} (u : Blocks k) :
    let P := scan (2 ^ (2 * k))
    BitRAM.Halts P [] (tape u) ∧ BitRAM.haltStep P [] (tape u) = 3 * 2 ^ (2 * k) + 1 ∧
      (BitRAM.finalState P [] (tape u)).mem = memory u ∧
      BitRAM.workingBits P [] (tape u) ≤ 5 * k + 5 := by
  let B := 2 ^ (2 * k)
  obtain ⟨a, b, ha, hb, h⟩ := boundary u B (le_refl _)
  have cmd : (scan B)[3 * B]? = some .halt := by
    rw [scan, List.getElem?_ofFn, dif_pos (by omega)]
    simp
  have last : scanRun u (3 * B + 1) =
      { scanRun u (3 * B) with
        pc := 3 * B + 1
        halted := true
        cost := (scanRun u (3 * B)).cost + 1 } := by
    rw [scan_step]
    simp [BitRAM.step, h.live, h.counter, cmd, B]
  have halts : BitRAM.Halts (scan B) [] (tape u) := ⟨3 * B + 1, by
    change (scanRun u _).halted = true
    rw [last]⟩
  have duration : BitRAM.haltStep (scan B) [] (tape u) = 3 * B + 1 := by
    classical
    unfold BitRAM.Halts at halts
    rw [BitRAM.haltStep, dif_pos halts, Nat.find_eq_iff]
    refine ⟨?_, fun t ht => ?_⟩
    · change (scanRun u _).halted = true
      rw [last]
    · change (scanRun u t).halted ≠ true
      rw [(before_halt u t (by change t ≤ 3 * B; omega)).1]
      decide
  refine ⟨halts, duration, ?_, ?_⟩
  · change (scanRun u (BitRAM.haltStep (scan B) [] (tape u))).mem = _
    rw [duration, last]
    exact h.written.trans (prefix_full u)
  · change (Finset.range (BitRAM.haltStep (scan B) [] (tape u) + 1)).sup
      (fun t => BitRAM.space (scanRun u t)) ≤ _
    rw [duration, Finset.sup_le_iff]
    intro t ht
    have ht' := Finset.mem_range.mp ht
    by_cases he : t = 3 * B + 1
    · rw [he, last]
      exact (before_halt u (3 * B) (le_refl _)).2
    · exact (before_halt u t (by change t ≤ 3 * B; omega)).2

/-- A single halting program for each width `k` can finish with any of
`2^(k * k)` different memories on suitable tapes. Its published peak working
space is linear throughout each such run, including all address registers.
The unrolled scan takes exponentially many steps. -/
theorem many_halting_memories (k : ℕ) :
    ∃ (P : BitRAM.Program) (memories : Finset (ℤ →₀ ℚ)), memories.card = 2 ^ (k * k) ∧
      ∀ m ∈ memories, ∃ ω, BitRAM.Halts P [] ω ∧ BitRAM.haltStep P [] ω = 3 * 2 ^ (2 * k) + 1 ∧
        (BitRAM.finalState P [] ω).mem = m ∧
        BitRAM.workingBits P [] ω ≤ 5 * k + 5 := by
  let emb : Blocks k ↪ (ℤ →₀ ℚ) :=
    ⟨memory, fun _ _ h => encode_injective k (by simp [encode, h])⟩
  refine ⟨scan (2 ^ (2 * k)), Finset.univ.map emb, ?_, ?_⟩
  · simp [Blocks, pow_mul]
  · intro m hm
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hm
    exact ⟨tape u, scan_finishes u⟩

#print axioms many_halting_memories

#print axioms many_states_at_same_space

end Audit.SparseAddresses1508
