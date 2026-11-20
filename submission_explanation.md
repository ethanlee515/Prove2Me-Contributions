# Disproof of Lemma D.17 (submission 173)

The universally quantified Lean statement of Lemma D.17 is false. A counterexample is

$$
n=m=0,\qquad Q=P=\varnothing,\qquad
\mathrm{proc}(E,a)=\mathrm{none},\qquad
\mathrm{board}=[\mathrm{true}].
$$

There are no students, so the row-validity premises and the assertion that every student accepts the board both hold vacuously. The public pair list is empty. Consequently, the mask has length zero and the comparison tape remaining after the mask is the single unused bit `[true]`.

The procedure stops immediately. By the published definition of `replay`, stopping with a nonempty tape returns `none`. The first conjunct of Lemma D.17 nevertheless requires an answer list `ans` for which that same replay returns `some ans`. This is a contradiction. The Lean proof establishes the negation of the entire quantified statement using this instance; it does not rely on the certificate-length conjunct.

This counterexample concerns the zero-student case admitted by the formal declaration. It does not establish that the lemma restricted to nonempty markets is false or, by itself, refute the paper's main asymptotic claim.

**Joint discovery.** This counterexample was identified by Yu-Fang Chen (Academia Sinica), Kai-Min Chung (Academia Sinica), Shih-Han Hung (National Taiwan University), and Yi Lee (University of Maryland).

Source: Zhang, Zhao, Xu, Xi, and Zhao, *Structural Complexity of Matching with Indifferences*, STOC 2027 submission, p. 99, Lemma D.17.
