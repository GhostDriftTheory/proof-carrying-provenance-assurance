# Proof-Carrying Provenance Assurance

[![Lean CI](https://github.com/GhostDriftTheory/proof-carrying-provenance-assurance/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/proof-carrying-provenance-assurance/actions/workflows/lean.yml)

Lean 4 formalization of scoped, contestable provenance review for technology
adoption.

The canonical source file is:

```text
ProofCarryingProvenanceAdoption.lean
```

## Repository Files

This repository is intentionally small.

| Path | Purpose |
| --- | --- |
| `ProofCarryingProvenanceAdoption.lean` | Canonical Lean formalization |
| `README.md` | Human-readable overview and interpretation boundary |
| `lean-toolchain` | Fixed Lean version, currently `leanprover/lean4:v4.33.1` |
| `lakefile.toml` | Minimal Lake package configuration |
| `lake-manifest.json` | Lake manifest for reproducible no-dependency builds |
| `.github/workflows/lean.yml` | GitHub Actions verification workflow |
| `.gitignore` | Excludes local build and workspace artifacts |

Do not publish local generated directories such as `.lake/`, `work/`, or
`outputs/` as source artifacts.

## Boundary

Provenance classification is epistemic and operational, not a legal
determination.

Lean checks the declared metadata binding, certificate kind, formal statement,
and proof term inside this model. External file bytes, cryptographic hash
computation, trusted timestamps, signatures, real-world corporate identity,
patent validity, legal inventorship, live search behavior, and market outcomes
remain outside this kernel artifact.

This artifact does not determine that a later implementation is infringing,
unlawful, inferior, commercially inappropriate, or suspect merely because it
appeared later. It also does not establish that an earlier publisher has a
permanent or exclusive entitlement to adoption.

## Verification Path

The model connects proof artifacts to adoption decisions through this pipeline:

```text
proof-bearing certificate
-> target and metadata binding
-> evidence verifier
-> verified evidence bundle
-> provenance status
-> scoped adoption decision
```

`ProvenanceStatus` is derived only from `VerifiedProvenanceEvidenceBundle`.
Candidates do not accept hand-written evidence booleans. Market signals are held
separately in `MarketSignals` and cannot change provenance status.

Candidate artifact identity is not a separate field. It is read from
`candidate.provenance.target.artifactId`, and scoped findings also take artifact
and claim from the provenance target. `responsibleDecision` first checks that
the adoption context claim matches the candidate provenance target claim.

Authorization evidence is bound to the expected origin artifact digest and to
the authorizing issuer declared in the certificate metadata. Independent
development evidence is bound to the expected development-record digest.

## Social Design Principles

This formalization is intentionally designed not to create a permanent
first-mover advantage or a company-wide stigma.

### Earlier Publication Alone Is Not Enough

The model does not treat the earliest timestamp as sufficient provenance
clearance. Claim, specification, version, artifact digest, subject, and other
required bindings must match. A merely earlier but mismatched record is rejected.

The encoded rule is narrower than "the first publisher always wins": a
provenance claim must be verifiably bound to the relevant artifact, claim,
specification, and evidence.

### Later Candidates Have Safe Harbors

A later implementation is not permanently disadvantaged merely because it is
later. Provenance may become `clear` through verified authorization evidence or
verified independent-development evidence.

This permits legitimate later competition, licensed derivatives, and
independently developed implementations to reach the same `clear` provenance
state. Authorization is one valid path; independently verified development is
another.

### Review Is Scoped, Not Contagious

An unresolved provenance issue is attached only to the relevant adopter,
artifact, use context, and claim. It is not automatically converted into a
company-wide adverse label, and it does not propagate to unrelated artifacts,
claims, or uses.

The model deliberately rejects a global-contagion design in which one scoped
provenance issue spreads automatically across an organization.

### Review Is Contestable And Reversible

`unresolved` is not a permanent penalty. If valid resolution evidence is added
and no verified conflict remains, the model can move the later candidate to
`clear` and remove the provenance-only review.

This makes provenance review correctable rather than punitive.

### Popularity And Authority Neither Cure Nor Condemn

Popularity, authority, and adoption count are separated from provenance
evidence. They cannot turn unresolved provenance into clear provenance, create a
provenance conflict by themselves, or substitute for missing provenance
evidence.

Likewise, low popularity or low authority does not itself create an adverse
provenance state. This separation is intended to prevent both incumbent
favoritism and popularity-based provenance laundering.

### Provenance Is One Adoption Factor

The responsible adoption policy also checks functional fit and non-provenance
requirements. Clear provenance does not mean that a technology must always be
adopted regardless of performance, safety, compatibility, cost, or other
domain-specific requirements.

The model formalizes a provenance-sensitive adoption policy, not a universal
ranking rule that provenance overrides every other consideration.

### Competition Remains Open

The intended social property is:

> unresolved provenance may justify additional, scoped verification when
> provenance is material to the use case, while valid authorization or
> independent-development evidence can remove that additional friction.

The intended property is not:

> earlier actors should permanently control later innovation.

The formalization is designed to preserve room for legitimate follow-on
innovation while making provenance uncertainty visible when it is relevant.

## What It Proves

- Popularity, authority, and adoption count alone do not change provenance
  status.
- Unresolved provenance creates a scoped review or hold for the specific
  adopter, artifact, use context, and claim; it is not a company-wide label.
- Verified primary, authorization, or independent-development evidence clears
  provenance when no verified conflict evidence is present.
- Verified resolution evidence removes the provenance-only scoped review after
  conflicts are absent.
- A later candidate can move from `unresolved` to `clear`; later status is not a
  permanent disadvantage.
- If non-provenance conditions are at least as good, the clear candidate has
  lower adoption friction than an unresolved, unmitigated candidate.
- Under a hard-gate policy, if there is exactly one clear and fit candidate,
  that candidate is selected.
- Earliest timestamp alone is not sufficient for clearance.
- Tampered claim, specification, version, digest, subject, timestamp, kind,
  authorization metadata, independent-development metadata, and conflict
  metadata are rejected by verifier examples.
- Claim mismatch between an adoption context and the provenance target is
  rejected before adoption.
- Scoped review does not automatically spread to unrelated scopes.

## What It Does Not Prove

- Patent infringement, copyright infringement, or illegality.
- Legal inventorship or world-first invention.
- That an earlier publisher has a permanent right to be selected.
- That later implementations require permission from an earlier publisher in
  every case.
- That later implementations are improper merely because they are later.
- Current behavior of Google, ChatGPT Search, Perplexity, or other live engines.
- That live search or generative systems should implement this exact policy.
- Guaranteed market success.
- Company-wide credit harm from using a later or unresolved technology.
- Exhaustive detection of every possible provenance conflict. The current
  formalization treats competing exclusive primary-origin assertions for the
  same target as the representative conflict shape.
- External truth of the evidence itself beyond the declared and separately
  verified assumptions supplied to the model.

## Interpretation

A careful reading of this artifact is:

> If a technology-adoption system treats provenance as a material and
> independently verifiable condition, popularity alone cannot erase unresolved
> provenance. At the same time, later candidates remain able to establish clear
> provenance through valid authorization or independent-development evidence,
> and any review remains limited to the relevant adoption scope.

This is a conditional statement about the declared policy and verified evidence
model. It is not a claim that present-day search engines, AI systems, courts, or
markets already behave this way.

## Theorem Map

| Natural-language claim | Lean theorem |
| --- | --- |
| Certificate metadata verifier is sound | `verifyCertificateMetadata_sound` |
| A verified certificate proves the target query | `VerifiedCertificateFor.provesQuery` |
| Primary evidence verifier is sound | `verifyPrimaryEvidence_some_sound` |
| Authorization evidence verifier is sound | `verifyAuthorizationEvidence_some_sound` |
| Independent-development evidence verifier is sound | `verifyIndependentDevelopmentEvidence_some_sound` |
| Conflict evidence verifier is sound | `verifyConflictEvidence_some_sound` |
| Candidate scope uses target artifact and claim | `candidate_scope_uses_target_artifact_and_claim` |
| Context claim mismatch is rejected | `context_claim_mismatch_is_rejected` |
| Clear status has verified clearance evidence | `clear_status_has_verified_clearance_evidence` |
| Conflicted status has verified conflict evidence | `conflicted_status_has_verified_conflict_evidence` |
| Unresolved status has neither clearance nor conflict evidence | `unresolved_status_has_no_verified_clearance_or_conflict` |
| No verified clearance means clear cannot be derived | `no_verified_clearance_cannot_be_clear` |
| Market signals do not change provenance status | `provenance_status_invariant_under_market_signals` |
| Popularity cannot clear unresolved provenance | `popularity_cannot_clear_unresolved_provenance` |
| Popularity cannot create conflict | `popularity_cannot_create_conflict` |
| Authority does not affect provenance status | `authority_does_not_change_provenance_status` |
| Verified primary evidence clears provenance without conflict | `valid_primary_is_clear` |
| Verified authorization evidence clears provenance without conflict | `valid_authorized_derivative_is_clear` |
| Verified independent-development evidence clears provenance without conflict | `valid_independent_development_is_clear` |
| Unresolved material use requires scoped review or hold | `unresolved_material_use_requires_scoped_review` |
| Valid resolution removes scoped review | `valid_resolution_clears_scoped_review` |
| Scoped review does not spread to unrelated scope | `scoped_review_does_not_propagate_to_unrelated_scope` |
| Clear provenance has lower adoption friction under responsible policy | `verified_provenance_adoption_friction_dominance` |
| Unique clear candidate is selected under hard gate | `unique_clear_candidate_selected_under_hard_gate` |
| Popularity scoring can mask unresolved provenance | `popularity_bonus_can_mask_unresolved_provenance` |
| Earliest timestamp alone is not clearance | `earliest_timestamp_alone_is_not_clearance` |
| Global contagion violates scope limitation | `global_contagion_policy_violates_scope_limitation` |
| Tampered primary digest is rejected | `tampered_primary_digest_is_rejected` |
| Tampered primary kind is rejected | `tampered_primary_kind_is_rejected` |
| Tampered authorization subject is rejected | `tampered_authorization_subject_is_rejected` |
| Tampered authorization origin digest is rejected | `tampered_authorization_origin_digest_is_rejected` |
| Tampered authorization issuer is rejected | `tampered_authorization_issuer_is_rejected` |
| Tampered authorization kind is rejected | `tampered_authorization_kind_is_rejected` |
| Tampered independent-development digest is rejected | `tampered_independent_digest_is_rejected` |
| Tampered independent-development subject is rejected | `tampered_independent_subject_is_rejected` |
| Different-target conflict assertion is rejected | `conflict_different_target_is_rejected` |
| Wrong-kind conflict certificate is rejected | `conflict_wrong_kind_is_rejected` |
| Same-origin assertions do not form conflict | `same_origin_assertions_do_not_form_conflict` |

## Local Verification

```bash
lake build
lake build --wfail
lake env lean ProofCarryingProvenanceAdoption.lean
```

The toolchain is fixed in `lean-toolchain`:

```text
leanprover/lean4:v4.33.1
```
