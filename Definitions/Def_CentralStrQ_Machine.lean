-- Prove2Me definition source: https://prove2.me/theorems/b41767cd-cd86-495c-ae47-d16d332de5a3
import Mathlib
import Definitions.Def_WordRAMEquivalence_Foundation1
import Definitions.Def_WordRAM_Complexity_Programs

set_option autoImplicit false

namespace CentralStrQ

open WordRAM

/-!
# The deterministic word RAM of Kempa–Kociumaka

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Section 3.2, p.13 (PDF p.14):
"For our upper bounds, we use the standard word RAM model of computation [Hag98] with w-bit
machine words, with w = Ω(log N) (where N is the size of the input), and all standard bitwise
and arithmetic operations take O(1) time." Remark 3.2, p.13: "The space usage of an algorithm is
the largest amount of memory occupied at any point during its execution, including the memory
holding its input and output."

**Formalization Note.**
* Words, memories, addresses (direct and indirect) and unsigned comparisons are the published
  core types of `WordRAMEquivalence_Foundation1` (Hagerup's word RAM, the paper's [Hag98]);
  operands are the published width-generic `WordRAM.Complexity.Operand`
  (`WordRAM_Complexity_Programs`).
* The instruction set is Hagerup's multiplication instruction set (copy, add, sub, mul, shl, shr,
  AND, OR, NOT, jumps and conditional jumps, immediate/direct/indirect operands) **plus** unsigned
  division and modulo (`BitVec.udiv`, `BitVec.umod`: `x / 0 = 0` and `x % 0 = x`). This is the
  reading of "all standard bitwise and arithmetic operations". No native constants.
* The program is **width-generic**: immediates are natural numbers, read as `BitVec.ofNat w v`
  (that is, modulo `2^w`), so one program runs at every word size.
* The instruction `call a` is the oracle call of `Def_CentralStrQ_OracleMachine`; in the plain
  machine it is stuck (the run never halts past it).
* Every executed instruction costs one step (`ticks`). `maxAddr` is one more than the largest
  address read or written so far, counting the pointer cell of an indirect operand.
* Fetching outside the program is stuck, not a halt.
-/

/-- An operand is the published width-generic `WordRAM.Complexity.Operand`: an immediate natural
number (truncated modulo `2^w` when read) or a memory cell. -/
abbrev Operand := WordRAM.Complexity.Operand

/-- The binary operations: Hagerup's multiplication set plus unsigned division and modulo. -/
inductive BinOp where
  | add | sub | mul | udiv | umod | shl | shr | band | bor
  deriving DecidableEq, Repr

/-- The width-generic instruction set. -/
inductive Instr where
  | copy (dst : Address) (src : Operand)
  | binary (op : BinOp) (dst : Address) (x y : Operand)
  | bitNot (dst : Address) (src : Operand)
  | jump (target : ℕ)
  | branch (cmp : Comparison) (x y : Operand) (target : ℕ)
  /-- Oracle call: cells `a`, `a+1`, `a+2` hold the instance address, the output address and
  the output budget. Stuck in the plain machine. -/
  | call (a : ℕ)
  | halt
  deriving DecidableEq, Repr

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program := List Instr

variable {w : Width}

/-- Arithmetic is modulo `2^w`; shifts are by the unsigned value of the second operand. -/
def BinOp.eval : BinOp → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .udiv, x, y => x / y
  | .umod, x, y => x % y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y

/-- The value of an operand at word size `w` (the published lowering, then the published read). -/
def opRead (mem : Memory w) (o : Operand) : Word w := (o.lower w).read mem

/-- The cells an address touches: the cell itself and, if indirect, the pointer cell. -/
def addrTouched (mem : Memory w) : Address → List ℕ
  | .direct a => [a]
  | .indirect a => [a, (mem a).toNat]

/-- The cells an operand reads. -/
def opTouched (mem : Memory w) : Operand → List ℕ
  | .immediate _ => []
  | .memory a => addrTouched mem a

/-- The cells an instruction reads or writes, evaluated before it executes. -/
def Instr.touched (mem : Memory w) : Instr → List ℕ
  | .copy d s => addrTouched mem d ++ opTouched mem s
  | .binary _ d x y => addrTouched mem d ++ opTouched mem x ++ opTouched mem y
  | .bitNot d s => addrTouched mem d ++ opTouched mem s
  | .branch _ x y _ => opTouched mem x ++ opTouched mem y
  | .call a => [a, a + 1, a + 2]
  | .jump _ | .halt => []

/-- One more than the largest cell in a list (`0` for the empty list). -/
def reachOf (l : List ℕ) : ℕ := l.foldr (fun a r => max (a + 1) r) 0

/-- A machine state: memory, program counter, halting flag, executed steps, and one more than
the largest address touched so far. -/
structure State (w : Width) where
  mem : Memory w
  pc : ℕ := 0
  halted : Bool := false
  ticks : ℕ := 0
  maxAddr : ℕ := 0

/-- The initial state on memory `mem`. -/
def State.init (mem : Memory w) : State w := { mem := mem }

/-- Execute one non-oracle instruction; `none` for `call` (stuck). -/
def exec1 (i : Instr) (s : State w) : Option (State w) :=
  let r := max s.maxAddr (reachOf (i.touched s.mem))
  let s' : State w := { s with pc := s.pc + 1, ticks := s.ticks + 1, maxAddr := r }
  match i with
  | .copy dst src => some { s' with mem := s.mem.write (dst.resolve s.mem) (opRead s.mem src) }
  | .binary op dst x y =>
      some { s' with mem := s.mem.write (dst.resolve s.mem) (op.eval (opRead s.mem x) (opRead s.mem y)) }
  | .bitNot dst src => some { s' with mem := s.mem.write (dst.resolve s.mem) (~~~(opRead s.mem src)) }
  | .jump target => some { s' with pc := target }
  | .branch cmp x y target =>
      some { s' with pc := if cmp.test (opRead s.mem x) (opRead s.mem y) then target else s.pc + 1 }
  | .call _ => none
  | .halt => some { s' with halted := true }

/-- One step of the plain machine; `none` if halted or stuck. -/
def step (P : Program) (s : State w) : Option (State w) :=
  if s.halted then none
  else match P[s.pc]? with
    | none => none
    | some i => exec1 i s

/-- Run for at most `k` steps (a halted or stuck state stays put). -/
def runN (P : Program) : ℕ → State w → State w
  | 0, s => s
  | k + 1, s => match step P s with
    | none => s
    | some t => runN P k t

/-- The memory holding the words `ws` in cells `0, …, |ws| − 1` and `rest` elsewhere
(Hagerup: memory "not assumed to be initialized in any particular way"). -/
def loadMem (ws : List ℕ) (rest : Memory w) : Memory w :=
  fun a => if h : a < ws.length then BitVec.ofNat w.bits ws[a] else rest a

/-- The cells `base, …, base + |ws| − 1` hold the words `ws` (as unsigned integers). -/
def HoldsAt (mem : Memory w) (base : ℕ) (ws : List ℕ) : Prop :=
  ∀ i (h : i < ws.length), (mem (base + i)).toNat = ws[i]

/-- Output convention: cell `0` holds a pointer `q`, the words `ws` are stored at
`q, …, q + |ws| − 1`, and this block ends at or below `reach`. -/
def OutputsAt (mem : Memory w) (ws : List ℕ) (reach : ℕ) : Prop :=
  HoldsAt mem (mem 0).toNat ws ∧ (mem 0).toNat + ws.length ≤ reach

/-- The run of `P` from `init` halts within `t` steps and its final memory and space usage
(one more than the largest touched address) satisfy `post`. -/
def RunsWithin (P : Program) (init : Memory w) (t : ℝ) (post : Memory w → ℕ → Prop) : Prop :=
  ∃ k : ℕ, (runN P k (State.init init)).halted = true ∧
    ((runN P k (State.init init)).ticks : ℝ) ≤ t ∧
    post (runN P k (State.init init)).mem (runN P k (State.init init)).maxAddr

end CentralStrQ
