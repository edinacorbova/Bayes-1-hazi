(*
  Lemma: 
  Ha létezik olyan x, amire A x ∧ B x igaz,
  akkor következik, hogy:
  - létezik olyan x, amire A x igaz, és
  - létezik olyan x, amire B x igaz.

  Formálisan:
  (∃x. A(x) ∧ B(x)) → (∃x. A(x)) ∧ (∃x. B(x))
*)

Lemma problem_4 : 
  forall (U : Type) (A B : U -> Prop), 
  (exists x, A x /\ B x) -> 
  (exists x, A x) /\ (exists x, B x).
Proof.
  (* Bevezetjük a típust, predikátumokat és a feltételt *)
  intros U A B [x [HA HB]].

  (* Két részre bontjuk a következtetést: /\ bal és jobb oldalára *)
  split.

  - (* Első rész: létezik x, amire A x igaz *)
    exists x. exact HA.

  - (* Második rész: létezik x, amire B x igaz *)
    exists x. exact HB.
Qed.
