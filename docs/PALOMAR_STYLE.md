# Palomar Challenge/Comparator style

Palomar compares elaborated Lean constants, not merely mathematical
equivalence or pretty-printed declaration types. For a definition it compares
the elaborated value too, including universe names and typeclass-instance paths
inside the body. Run this before every submission:

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
- Audit every `definition_names` body and every concrete definition reached
  transitively from a compared theorem or instance. A matching parent body is
  insufficient when it refers to a named child definition whose value differs.
- Write order operations with explicit `@LE.le` instance paths when Challenge
  and Solution import graphs can elaborate `≤` through different parent
  structures. `ScottMap.le` exposed this exact failure mode.

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
2. compared names, universe parameters, types, all `definition_names` values,
   and transitively locked bodies match;
3. locked bodies contain no generated `._proof_N` dependencies;
4. Solution sources contain no `sorry`;
5. Solution theorem axioms are permitted by `comparator.json`; and
6. the patch has no whitespace errors.

Treat a green `lake build` alone as insufficient.
