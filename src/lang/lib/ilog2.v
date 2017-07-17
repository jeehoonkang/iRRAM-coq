From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iRRAM.lang Require Import proofmode notation.
Require Import Reals.
Set Default Proof Using "Type".

Definition ilog2 : val :=
  λ: "x",
  let: "l" := ref #1 in
  (if: #(3/2) <(#(-1)) "x"
   then let: "y" := ref "x" in
        while: (#(5/2) <(#(-1)) !"y")
        do ("l" <- !"l" + #1;; "y" <- !"y" / #(2))
   else while: (#3 * #2 ^ (!"l" - #2) <(!"l"-#2) !"x")
        do ("l" <- !"l" - #1)) (* FIXME: repeat, until *)
  ;;
  !"l".

Section proof.
  Context `{!heapG Σ} (N : namespace).

  Lemma ilog2_spec (R : iProp Σ) x:
    {{{ ⌜(x > 0)%R⌝ }}}
      ilog2 (Lit $ LitREAL $ x)
    {{{ l, RET #l; ⌜(Rpower 2 (IZR (l-1)) < x /\ x < (Rpower 2 (IZR (l+1))))%R⌝ }}}.
  Proof.
    iIntros (Φ HR) "HΦ". rewrite -wp_fupd /ilog2 /=.
    wp_seq. wp_alloc l as "Hl". wp_seq.
    admit.
  Admitted.
End proof.
