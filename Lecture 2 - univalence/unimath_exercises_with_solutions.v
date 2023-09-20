Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* The unit type is contractible.*)

Print unit.

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    unfold iscontr.
    use tpair.
    - exact tt.
    - simpl.
      intro t.
      induction t.
      apply idpath.
Defined.

(* Exericse 2 *)

(* The empty type is a proposition. *)

Theorem empty_is_prop : isaprop (∅).
    Proof.
        unfold isaprop.
        simpl.
        intros x y.
        induction x.
Defined.

(* Exercise 3 *)

(* Every contractible type is a proposition. *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.

Theorem contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
    unfold isaprop.
    simpl.
    intros x y.
    unfold iscontr.
    use tpair.
    destruct h as [cntr p].
    + exact (path_combination (p x) (p y)).
    + simpl.
      intro t.
      induction t.
      exact (path_combination_fact (pr2 h x)).
Defined.

(* Exercise 4 *)

(* If a proposition is inhabited, then it is contractible.*)

Theorem inhab_prop_is_contr {P : UU} (p : P) (h : isaprop P) : iscontr P.
Proof.
    use tpair.
    - exact p. 
    - simpl.
      intro q.
      unfold isaprop in h.
      simpl isofhlevel in h.
      set (e := h q p).
      exact (pr1 e).
Defined.

(* Exercise 5 *)

(* If a type has h-level n, then it has h-level n+1.*)

Lemma hlevel_cumulativ_ind  (n : nat) : ∏ (T : UU) (h : isofhlevel n T), isofhlevel (S n) T.
Proof.
    induction n.
    - intros T c.
      exact (contr_is_prop c).
    - intros T h.
      simpl isofhlevel.
      intros x y.
      simpl isofhlevel in h.
      exact (IHn (x = y) (h x y)).
Defined.

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
    apply hlevel_cumulativ_ind.
    exact h.
Defined.