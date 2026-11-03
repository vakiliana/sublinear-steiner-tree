module

public import SteinerUpperBound.EstimatorLoop

@[expose] public section

namespace SteinerUpperBound.EstimatorLoop

open scoped Classical BigOperators

variable {I : Type*}

theorem record_unique (records : List (ScaleRecord I))
    (hn : (records.map ScaleRecord.index).Nodup)
    {r s : ScaleRecord I} (hr : r ∈ records) (hs : s ∈ records) (he : r.index = s.index) :
    r = s := by
  induction records generalizing r s with
  | nil => simp at hr
  | cons a records ih =>
      have h := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hr with hra | hr
      · rcases List.mem_cons.mp hs with hsa | hs
        · exact hra.trans hsa.symm
        · exact (h.1 (List.mem_map.mpr
            ⟨s, hs, he.symm.trans (congrArg ScaleRecord.index hra)⟩)).elim
      · rcases List.mem_cons.mp hs with hsa | hs
        · exact (h.1 (List.mem_map.mpr
            ⟨r, hr, he.trans (congrArg ScaleRecord.index hsa)⟩)).elim
        · exact ih h.2 hr hs he

theorem complete_records {length : ℕ} (records : List (ScaleRecord (Fin length)))
    (hlog : records.map ScaleRecord.index = (List.finRange length).reverse)
    (R : Fin length → ℝ → ℝ → Prop)
    (hR : ∀ r ∈ records, R r.index r.saving r.band) (scale : Fin length → ℝ) :
    ∃ Z T : Fin length → ℝ, (∀ i, R i (Z i) (T i)) ∧
      (records.map (fun r => scale r.index * r.saving)).sum = ∑ i, scale i * Z i ∧
      (records.map ScaleRecord.band).sum = ∑ i, T i := by
  classical
  have hn : (records.map ScaleRecord.index).Nodup := by
    rw [hlog]
    simpa only [List.nodup_reverse] using List.nodup_finRange length
  have hex (i : Fin length) : ∃ r ∈ records, r.index = i := by
    apply List.mem_map.mp
    rw [hlog]
    simp
  choose rs hrs his using hex
  let Z := fun i => (rs i).saving
  let T := fun i => (rs i).band
  have hsaving (r : ScaleRecord (Fin length)) (hr : r ∈ records) : r.saving = Z r.index := by
    have h := record_unique records hn (hrs r.index) hr (his r.index)
    exact (congrArg ScaleRecord.saving h).symm
  have hband (r : ScaleRecord (Fin length)) (hr : r ∈ records) : r.band = T r.index := by
    have h := record_unique records hn (hrs r.index) hr (his r.index)
    exact (congrArg ScaleRecord.band h).symm
  refine ⟨Z, T, ?_, ?_, ?_⟩
  · intro i
    simpa only [his i] using hR (rs i) (hrs i)
  · calc
      _ = (records.map (fun r => scale r.index * Z r.index)).sum := by
        congr 1
        apply List.map_congr_left
        intro r hr
        rw [hsaving r hr]
      _ = ((records.map ScaleRecord.index).map (fun i => scale i * Z i)).sum := by
        rw [List.map_map]
        rfl
      _ = _ := by
        rw [hlog, List.map_reverse, List.sum_reverse]
        exact (Fin.sum_univ_def (fun i => scale i * Z i)).symm
  · calc
      _ = (records.map (fun r => T r.index)).sum := by
        congr 1
        apply List.map_congr_left
        intro r hr
        exact hband r hr
      _ = ((records.map ScaleRecord.index).map T).sum := by rw [List.map_map]; rfl
      _ = _ := by
        rw [hlog, List.map_reverse, List.sum_reverse]
        exact (Fin.sum_univ_def T).symm

end SteinerUpperBound.EstimatorLoop
