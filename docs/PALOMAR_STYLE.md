# Palomar Challenge/Comparator style

Palomar compares elaborated Lean constants, not merely mathematical
equivalence or pretty-printed declarations. Run this before every submission:

```bash
scripts/palomar_preflight.sh
```

## Compared declarations

- Pin universe names (`Type u`, `Type v`). Comparator compares `levelParams`,
  including their names.
- Keep instance paths explicit where elaboration could choose different
  equivalent instances.
- A `theorem_names` entry must be a theorem; a `definition_names` entry must be
  a definition, not a structure or instance.
- Keep concrete Challenge and Solution definition bodies structurally
  identical. Do not rely on proof irrelevance to make values compare.

## Concrete structures

Never put an inline proof in a structure value that is definition-locked:

```lean
-- Avoid: creates `instPartialOrder._proof_N`.
instance : PartialOrder A where
  le_refl x := ...

-- Use: the structure body refers to a stable theorem name.
theorem order_refl (x : A) : rel x x := by ...
instance : PartialOrder A where
  le_refl := order_refl
```

Put each named proof boundary in `comparator.json` under `theorem_names`.
Challenge may use `sorry`; Solution supplies the proof. This fixes the concrete
data while allowing proof terms to differ.

## Submission checklist

The preflight must confirm:

1. the full project builds;
2. compared names, universe parameters, types, and locked bodies match;
3. locked bodies contain no generated `._proof_N` dependencies;
4. Solution sources contain no `sorry`;
5. Solution theorem axioms are permitted by `comparator.json`; and
6. the patch has no whitespace errors.

Treat a green `lake build` alone as insufficient.
