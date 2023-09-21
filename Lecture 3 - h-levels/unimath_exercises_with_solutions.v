Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    unfold weq in e.
    destruct e as [f w].
    intro b.
    unfold isweq in w.
    unfold iscontr in w.
    destruct (w b) as [cntr _].
    unfold hfiber in cntr.
    destruct cntr as [x _].
    exact x.
Defined.

(* Exercise 2 *)

(* A contractible type is connected.*)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

Theorem contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
    destruct h as [h1 h2].
    exact (path_combination (h2 x) (h2 y)).
Defined.

(* Exercise 3 *)

(* Any contractible type is equivalent to the unit type.*)

(* Hint: use ~contr_is_prop~ and ~unit_iscontr~ that were shown in the last exercise set. *)

Lemma contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
    Admitted.

Lemma unit_iscontr : iscontr unit.
Proof.
    Admitted.

Lemma paths_in_unit (p : tt = tt) : p = (idpath tt).
Proof.
    exact (contr_to_path (contr_is_prop unit_iscontr tt tt) p (idpath tt)).
Defined.

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    unfold weq.
    use tpair.
    - exact (λ _ , tt).
    - simpl.
      unfold isweq.
      intro y.
      induction y.
      unfold hfiber.
      destruct h as [cntr p].
      use tpair.
      + exact (cntr,,idpath tt).
      + simpl.
        intro t.
        destruct t as [c q].
        rewrite (p c).
        rewrite (paths_in_unit q).
        exact (idpath (cntr,, idpath tt)).
Defined.

(* Exercise 4*)

(* Difficult *)

(* Every statement ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Lemma iscontr_prop {A : UU} : isaprop (iscontr A).
Proof.
    unfold isaprop.
    simpl isofhlevel.
    intros [cntr1 c1] [cntr2 c2].
    set (A_is_contr := (cntr1,,c1)).
    assert (h1 : ∏ x : A, (iscontr (∏ t : A, t = x))).
    {
        intro.
        apply impred_iscontr.
        intro.
        use contr_is_prop.
        exact A_is_contr.
    }
    assert (h2 : iscontr (∑ cntr : A, ∏ t : A, t = cntr)).
    {
        use (isofhleveltotal2 0).
        - exact A_is_contr.
        - intro a.
          simpl.
          exact (h1 a). 
    }
    apply contr_is_prop.
    exact h2.
Defined.

Lemma hlevelprop_ind (n : nat) : ∏ A : UU, isaprop (isofhlevel n A).
Proof.
    induction n.
    - intro A.
      use iscontr_prop.
    - intro A.
      intros x y.
      simpl in x, y.
      set (h1 := λ a b : A, IHn (a = b)).
      assert (isaprop (∏ a b : A, isofhlevel n (a = b))).
      {
       use impred_isaprop.
       simpl.
       intro a. 
       use impred_isaprop.
       intro b.
       simpl.
       apply h1.
      }
      apply X.
Defined.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
    apply hlevelprop_ind.
Defined.