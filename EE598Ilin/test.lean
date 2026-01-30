import Mathlib

theorem fg_implies_acc (R : Type*) [CommRing R]
    (hFG : ∀ I : Ideal R, I.FG)
    (chain : ℕ →o Ideal R) :
    ∃ n, ∀ m, n ≤ m → chain n = chain m := sorry

theorem IsNoetherianRing.ascending_chain_stabilizes (R : Type*) [CommRing R] [IsNoetherianRing R]
    (chain : OrderHom Nat (Ideal R)) :
    Exists fun n => forall m, n <= m -> chain n = chain m := by
  -- The range {chain n | n} is a nonempty set of ideals
  set S := Set.range chain with hS_def
  have hne : S.Nonempty := Set.range_nonempty chain
  -- By Noetherianity, S has a maximal element
  obtain ⟨M, ⟨k, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance S hne
  -- For all m >= k, chain k = chain m
  refine ⟨k, fun m hm => ?_⟩
  -- chain k ≤ chain m since the chain is ascending
  have h1 : chain k <= chain m := chain.mono hm
  -- chain m ≤ chain k since chain k is maximal in S
  have h2 : chain m <= chain k := by
    by_contra h
    exact hmax (chain m) ⟨m, rfl⟩ (lt_of_le_of_ne h1 (fun heq => h (heq ▸ le_refl _)))
  exact le_antisymm h1 h2

theorem IsNoetherianRing.acc' (R : Type*) [CommRing R] [IsNoetherianRing R]
    (chain : OrderHom Nat (Ideal R)) :
    Exists fun n => forall m, n <= m -> chain n = chain m := by
  set S := Set.range chain
  have hne : S.Nonempty := Set.range_nonempty chain
  have hmax : Exists fun M =>
      S M /\ forall I, S I -> Not (M < I) :=
    sorry -- set_has_maximal_iff_noetherian
  have hk : Nat := sorry -- obtain k from hmax
  have hmax' : forall I, S I -> Not (chain hk < I) :=
    sorry -- maximality from hmax
  suffices forall m, hk <= m -> chain hk = chain m from
    Exists.intro hk this
  intro m hm
  have h1 : chain hk <= chain m := sorry -- ascending chain
  have h2 : chain m <= chain hk := sorry -- maximality of chain hk in S
  exact le_antisymm h1 h2

theorem IsNoetherianRing.acc [CommRing R] [IsNoetherianRing R]
    (chain : OrderHom Nat (Ideal R)) :
    Exists fun n => forall m, n <= m -> chain n = chain m := by
  set S := Set.range chain
  have hne : S.Nonempty := Set.range_nonempty chain
  have hmax : Exists fun M =>
      S M /\ forall I, S I -> Not (M < I) :=
    sorry -- set_has_maximal_iff_noetherian
  have hk : Nat := sorry -- obtain k from hmax
  have hmax' : forall I, S I -> Not (chain hk < I) :=
    sorry -- maximality from hmax
  suffices forall m, hk <= m -> chain hk = chain m from
    Exists.intro hk this
  intro m hm
  have h1 : chain hk <= chain m := sorry -- ascending chain
  have h2 : chain m <= chain hk := sorry -- maximality of chain hk in S
  exact le_antisymm h1 h2
