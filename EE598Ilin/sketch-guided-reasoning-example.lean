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

theorem IsNoetherianRing.acc'' [CommRing R] [IsNoetherianRing R]
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

/-- A noetherian ring (where by definition every ideal is finitely
generated) satisfies the ascending chain condition
-/
theorem IsNoetherianRing.acc [CommRing R] [IsNoetherianRing R]
    (I : ℕ → Ideal R) (h_chain : ∀ k, I k ≤ I (k + 1)) :
   ∃ n, ∀ m ≥ n, I n = I   m := by
  -- let J be the union of the ideals I n
  let J : Ideal R := ⨆ n, I n
  -- Since R is noetherian, J is finitely generated
  have J_fg : J.FG := IsNoetherian.noetherian J
  -- Let G be a finite set of generators of J
  obtain ⟨G : Finset R, hs : Ideal.span (↑G) = J⟩ := J_fg
  -- Choose n such that each generator g ∈ G is in Iₙ
  have h : ∃ n, ∀ g ∈ G, g ∈ I n := by
    sorry
    -- << for each g ∈ G, ∃ n_g, g ∈ I n_g.  Take n = max {n_g | g ∈ G} >>
  obtain ⟨n, hn⟩ := h
  -- Let's show that the n obtained from h works
  have h2 :  ∀ m ≥ n, I n = I m := by
    sorry
    -- << since every generator of J is in I n, J = I n.
    -- for each m ≥ n, since I n ≤ I m ≤ J, we have I n = I m >>
  use n
