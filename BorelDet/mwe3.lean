theorem test : ∃ n, n = 0 := ⟨0, rfl⟩
--example := by have h := test.2; exact 0 --this should fail, but before reaching the kernel
