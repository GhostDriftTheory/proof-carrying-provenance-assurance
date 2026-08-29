/-
Proof-Carrying Provenance Assurance

This single-file Lean artifact formalizes an operational provenance gate for
technology adoption. The path is:

  proof artifact -> target and metadata binding -> evidence verifier ->
  verified evidence bundle -> provenance status -> scoped adoption decision.

Boundary:
Provenance classification is epistemic and operational, not a legal
determination. The verifier checks metadata binding and Lean proof terms inside
the declared model. It does not verify external file bytes, real-world
signatures, trusted timestamps, legal authorization, legal inventorship, patent
validity, live search-engine behavior, or market success unless those facts are
provided as separately verified assumptions.
-/

import Std

set_option autoImplicit false

namespace ProofCarryingProvenance

universe u

/-! ## 1. Identifiers, targets, queries, and certificates -/

abbrev AgentId := String
abbrev ArtifactId := String
abbrev ClaimId := String
abbrev UseContextId := String
abbrev SpecificationId := String
abbrev SpecificationVersion := String
abbrev ArtifactDigest := String
abbrev IssuerId := String
abbrev CertificateId := String
abbrev Timestamp := Nat

inductive ProvenanceCertificateKind where
  | primary
  | authorization
  | independentDevelopment
  | conflict
deriving DecidableEq

structure ProvenanceTarget where
  artifactId : ArtifactId
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  primaryPublishedAt : Timestamp
  expectedOriginArtifactDigest : ArtifactDigest
  authorizingAgentId : AgentId
  authorizationId : String
  expectedDevelopmentRecordDigest : ArtifactDigest
  developmentRecordId : String
deriving DecidableEq

structure ProvenanceCertificateMeta where
  certificateId : CertificateId
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  issuerId : IssuerId
  issuedAt : Timestamp
  certificateKind : ProvenanceCertificateKind
deriving DecidableEq

structure CertifiedProvenanceClaim where
  metadata : ProvenanceCertificateMeta
  statement : Prop
  proof : statement

structure ProvenanceQuery where
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  issuerId : IssuerId
  statement : Prop

def queryTargets
    (target : ProvenanceTarget)
    (query : ProvenanceQuery) : Prop :=
  query.claimId = target.claimId /\
  query.specificationId = target.specificationId /\
  query.specificationVersion = target.specificationVersion /\
  query.artifactDigest = target.artifactDigest /\
  query.subjectAgentId = target.subjectAgentId

instance (target : ProvenanceTarget) (query : ProvenanceQuery) :
    Decidable (queryTargets target query) := by
  unfold queryTargets
  infer_instance

def CertificateMetadataMatches
    (expectedKind : ProvenanceCertificateKind)
    (query : ProvenanceQuery)
    (certificate : CertifiedProvenanceClaim) : Prop :=
  certificate.metadata.certificateKind = expectedKind /\
  certificate.metadata.claimId = query.claimId /\
  certificate.metadata.specificationId = query.specificationId /\
  certificate.metadata.specificationVersion = query.specificationVersion /\
  certificate.metadata.artifactDigest = query.artifactDigest /\
  certificate.metadata.subjectAgentId = query.subjectAgentId /\
  certificate.metadata.issuerId = query.issuerId

instance
    (expectedKind : ProvenanceCertificateKind)
    (query : ProvenanceQuery)
    (certificate : CertifiedProvenanceClaim) :
    Decidable
      (CertificateMetadataMatches expectedKind query certificate) := by
  unfold CertificateMetadataMatches
  infer_instance

def verifyCertificateMetadata
    (expectedKind : ProvenanceCertificateKind)
    (query : ProvenanceQuery)
    (certificate : CertifiedProvenanceClaim) : Bool :=
  decide (CertificateMetadataMatches expectedKind query certificate)

theorem verifyCertificateMetadata_sound
    {expectedKind : ProvenanceCertificateKind}
    {query : ProvenanceQuery}
    {certificate : CertifiedProvenanceClaim}
    (h :
      verifyCertificateMetadata expectedKind query certificate = true) :
    CertificateMetadataMatches expectedKind query certificate := by
  unfold verifyCertificateMetadata at h
  exact of_decide_eq_true h

theorem verifyCertificateMetadata_complete
    {expectedKind : ProvenanceCertificateKind}
    {query : ProvenanceQuery}
    {certificate : CertifiedProvenanceClaim}
    (h :
      CertificateMetadataMatches expectedKind query certificate) :
    verifyCertificateMetadata expectedKind query certificate = true := by
  unfold verifyCertificateMetadata
  exact decide_eq_true h

structure VerifiedCertificateFor
    (expectedKind : ProvenanceCertificateKind)
    (query : ProvenanceQuery) where
  certificate : CertifiedProvenanceClaim
  metadataAccepted :
    verifyCertificateMetadata expectedKind query certificate = true
  sameStatement : certificate.statement = query.statement

namespace VerifiedCertificateFor

theorem provesQuery
    {expectedKind : ProvenanceCertificateKind}
    {query : ProvenanceQuery}
    (verified : VerifiedCertificateFor expectedKind query) :
    query.statement := by
  have _metadataSound :
      CertificateMetadataMatches expectedKind query verified.certificate :=
    verifyCertificateMetadata_sound verified.metadataAccepted
  exact Eq.mp verified.sameStatement verified.certificate.proof

end VerifiedCertificateFor

def ProvenanceCertificateMatches
    (query : ProvenanceQuery)
    (certificate : CertifiedProvenanceClaim) : Prop :=
  CertificateMetadataMatches certificate.metadata.certificateKind
    query certificate /\
  certificate.statement = query.statement

theorem matched_provenance_certificate_proves_query
    {query : ProvenanceQuery}
    {certificate : CertifiedProvenanceClaim}
    (hMatches : ProvenanceCertificateMatches query certificate) :
    query.statement := by
  exact Eq.mp hMatches.right certificate.proof

/-! ## 2. Primary, authorization, independent, and conflict evidence -/

structure DeclaredPrimaryOrigin where
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  publishedAt : Timestamp
deriving DecidableEq

structure PrimaryEvidenceRecord where
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  publishedAt : Timestamp
deriving DecidableEq

def PrimaryWithinDeclaredUniverse
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord) : Prop :=
  record.claimId = declared.claimId /\
  record.specificationId = declared.specificationId /\
  record.specificationVersion = declared.specificationVersion /\
  record.artifactDigest = declared.artifactDigest /\
  record.subjectAgentId = declared.subjectAgentId /\
  record.publishedAt = declared.publishedAt

instance
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord) :
    Decidable (PrimaryWithinDeclaredUniverse declared record) := by
  unfold PrimaryWithinDeclaredUniverse
  infer_instance

def PrimaryEvidenceTargets
    (target : ProvenanceTarget)
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord) : Prop :=
  declared.claimId = target.claimId /\
  declared.specificationId = target.specificationId /\
  declared.specificationVersion = target.specificationVersion /\
  declared.artifactDigest = target.artifactDigest /\
  declared.subjectAgentId = target.subjectAgentId /\
  declared.publishedAt = target.primaryPublishedAt /\
  record.claimId = target.claimId /\
  record.specificationId = target.specificationId /\
  record.specificationVersion = target.specificationVersion /\
  record.artifactDigest = target.artifactDigest /\
  record.subjectAgentId = target.subjectAgentId /\
  record.publishedAt = target.primaryPublishedAt

instance
    (target : ProvenanceTarget)
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord) :
    Decidable (PrimaryEvidenceTargets target declared record) := by
  unfold PrimaryEvidenceTargets
  infer_instance

def primaryEvidenceQuery
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord) : ProvenanceQuery :=
  {
    claimId := declared.claimId,
    specificationId := declared.specificationId,
    specificationVersion := declared.specificationVersion,
    artifactDigest := declared.artifactDigest,
    subjectAgentId := declared.subjectAgentId,
    issuerId := declared.subjectAgentId,
    statement := PrimaryWithinDeclaredUniverse declared record
  }

structure VerifiedPrimaryEvidence
    (target : ProvenanceTarget) where
  declared : DeclaredPrimaryOrigin
  record : PrimaryEvidenceRecord
  certificate :
    VerifiedCertificateFor ProvenanceCertificateKind.primary
      (primaryEvidenceQuery declared record)
  targetAccepted : PrimaryEvidenceTargets target declared record

def verifyPrimaryEvidence?
    (target : ProvenanceTarget)
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord)
    (certificate : CertifiedProvenanceClaim)
    (sameStatement :
      certificate.statement =
        (primaryEvidenceQuery declared record).statement) :
    Option (VerifiedPrimaryEvidence target) :=
  if hMeta :
      verifyCertificateMetadata ProvenanceCertificateKind.primary
        (primaryEvidenceQuery declared record) certificate = true then
    if hTarget : PrimaryEvidenceTargets target declared record then
      some {
        declared := declared,
        record := record,
        certificate := {
          certificate := certificate,
          metadataAccepted := hMeta,
          sameStatement := sameStatement
        },
        targetAccepted := hTarget
      }
    else
      none
  else
    none

theorem verifyPrimaryEvidence_some_sound
    {target : ProvenanceTarget}
    {declared : DeclaredPrimaryOrigin}
    {record : PrimaryEvidenceRecord}
    {certificate : CertifiedProvenanceClaim}
    {sameStatement :
      certificate.statement =
        (primaryEvidenceQuery declared record).statement}
    {verified : VerifiedPrimaryEvidence target}
    (_h :
      verifyPrimaryEvidence? target declared record certificate
        sameStatement = some verified) :
    PrimaryWithinDeclaredUniverse verified.declared verified.record := by
  exact VerifiedCertificateFor.provesQuery verified.certificate

structure AuthorizationEvidenceRecord where
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  derivativeArtifactDigest : ArtifactDigest
  derivativeSubjectAgentId : AgentId
  originArtifactDigest : ArtifactDigest
  authorizingAgentId : AgentId
  authorizationId : String
deriving DecidableEq

def AuthorizationRecordInternallyValid
    (record : AuthorizationEvidenceRecord) : Prop :=
  Not (record.originArtifactDigest = "") /\
  Not (record.authorizationId = "")

instance (record : AuthorizationEvidenceRecord) :
    Decidable (AuthorizationRecordInternallyValid record) := by
  unfold AuthorizationRecordInternallyValid
  infer_instance

def AuthorizationEvidenceTargets
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord) : Prop :=
  record.claimId = target.claimId /\
  record.specificationId = target.specificationId /\
  record.specificationVersion = target.specificationVersion /\
  record.derivativeArtifactDigest = target.artifactDigest /\
  record.derivativeSubjectAgentId = target.subjectAgentId /\
  record.originArtifactDigest =
    target.expectedOriginArtifactDigest /\
  record.authorizingAgentId = target.authorizingAgentId /\
  record.authorizationId = target.authorizationId

instance
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord) :
    Decidable (AuthorizationEvidenceTargets target record) := by
  unfold AuthorizationEvidenceTargets
  infer_instance

def AuthorizedDerivativeWithinDeclaredUniverse
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord) : Prop :=
  AuthorizationRecordInternallyValid record /\
  AuthorizationEvidenceTargets target record

instance
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord) :
    Decidable
      (AuthorizedDerivativeWithinDeclaredUniverse target record) := by
  unfold AuthorizedDerivativeWithinDeclaredUniverse
  infer_instance

def verifyAuthorizationRecordBinding
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord) : Bool :=
  decide (AuthorizedDerivativeWithinDeclaredUniverse target record)

def authorizationEvidenceQuery
    (record : AuthorizationEvidenceRecord) : ProvenanceQuery :=
  {
    claimId := record.claimId,
    specificationId := record.specificationId,
    specificationVersion := record.specificationVersion,
    artifactDigest := record.derivativeArtifactDigest,
    subjectAgentId := record.derivativeSubjectAgentId,
    issuerId := record.authorizingAgentId,
    statement := AuthorizationRecordInternallyValid record
  }

structure VerifiedAuthorizationEvidence
    (target : ProvenanceTarget) where
  record : AuthorizationEvidenceRecord
  certificate :
    VerifiedCertificateFor ProvenanceCertificateKind.authorization
      (authorizationEvidenceQuery record)
  targetAccepted : AuthorizationEvidenceTargets target record

def verifyAuthorizationEvidence?
    (target : ProvenanceTarget)
    (record : AuthorizationEvidenceRecord)
    (certificate : CertifiedProvenanceClaim)
    (sameStatement :
      certificate.statement =
        (authorizationEvidenceQuery record).statement) :
    Option (VerifiedAuthorizationEvidence target) :=
  if hMeta :
      verifyCertificateMetadata ProvenanceCertificateKind.authorization
        (authorizationEvidenceQuery record) certificate = true then
    if hTarget :
        AuthorizationEvidenceTargets target record then
      some {
        record := record,
        certificate := {
          certificate := certificate,
          metadataAccepted := hMeta,
          sameStatement := sameStatement
        },
        targetAccepted := hTarget
      }
    else
      none
  else
    none

theorem verifyAuthorizationEvidence_some_sound
    {target : ProvenanceTarget}
    {record : AuthorizationEvidenceRecord}
    {certificate : CertifiedProvenanceClaim}
    {sameStatement :
      certificate.statement =
        (authorizationEvidenceQuery record).statement}
    {verified : VerifiedAuthorizationEvidence target}
    (_h :
      verifyAuthorizationEvidence? target record certificate
        sameStatement = some verified) :
    AuthorizedDerivativeWithinDeclaredUniverse target verified.record := by
  exact And.intro
    (VerifiedCertificateFor.provesQuery verified.certificate)
    verified.targetAccepted

structure IndependentDevelopmentEvidenceRecord where
  claimId : ClaimId
  specificationId : SpecificationId
  specificationVersion : SpecificationVersion
  artifactDigest : ArtifactDigest
  subjectAgentId : AgentId
  developmentRecordDigest : ArtifactDigest
  developmentRecordId : String
deriving DecidableEq

def IndependentDevelopmentRecordInternallyValid
    (record : IndependentDevelopmentEvidenceRecord) : Prop :=
  Not (record.developmentRecordId = "") /\
  Not (record.developmentRecordDigest = "")

instance (record : IndependentDevelopmentEvidenceRecord) :
    Decidable
      (IndependentDevelopmentRecordInternallyValid record) := by
  unfold IndependentDevelopmentRecordInternallyValid
  infer_instance

def IndependentDevelopmentEvidenceTargets
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord) : Prop :=
  record.claimId = target.claimId /\
  record.specificationId = target.specificationId /\
  record.specificationVersion = target.specificationVersion /\
  record.artifactDigest = target.artifactDigest /\
  record.subjectAgentId = target.subjectAgentId /\
  record.developmentRecordId = target.developmentRecordId /\
  record.developmentRecordDigest =
    target.expectedDevelopmentRecordDigest

instance
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord) :
    Decidable
      (IndependentDevelopmentEvidenceTargets target record) := by
  unfold IndependentDevelopmentEvidenceTargets
  infer_instance

def IndependentDevelopmentWithinDeclaredUniverse
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord) : Prop :=
  IndependentDevelopmentRecordInternallyValid record /\
  IndependentDevelopmentEvidenceTargets target record

instance
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord) :
    Decidable
      (IndependentDevelopmentWithinDeclaredUniverse target record) := by
  unfold IndependentDevelopmentWithinDeclaredUniverse
  infer_instance

def verifyIndependentDevelopmentRecordBinding
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord) : Bool :=
  decide (IndependentDevelopmentWithinDeclaredUniverse target record)

def independentDevelopmentEvidenceQuery
    (record : IndependentDevelopmentEvidenceRecord) : ProvenanceQuery :=
  {
    claimId := record.claimId,
    specificationId := record.specificationId,
    specificationVersion := record.specificationVersion,
    artifactDigest := record.artifactDigest,
    subjectAgentId := record.subjectAgentId,
    issuerId := record.subjectAgentId,
    statement :=
      IndependentDevelopmentRecordInternallyValid record
  }

structure VerifiedIndependentDevelopmentEvidence
    (target : ProvenanceTarget) where
  record : IndependentDevelopmentEvidenceRecord
  certificate :
    VerifiedCertificateFor
      ProvenanceCertificateKind.independentDevelopment
      (independentDevelopmentEvidenceQuery record)
  targetAccepted :
    IndependentDevelopmentEvidenceTargets target record

def verifyIndependentDevelopmentEvidence?
    (target : ProvenanceTarget)
    (record : IndependentDevelopmentEvidenceRecord)
    (certificate : CertifiedProvenanceClaim)
    (sameStatement :
      certificate.statement =
        (independentDevelopmentEvidenceQuery record).statement) :
    Option (VerifiedIndependentDevelopmentEvidence target) :=
  if hMeta :
      verifyCertificateMetadata
        ProvenanceCertificateKind.independentDevelopment
        (independentDevelopmentEvidenceQuery record)
        certificate = true then
    if hTarget :
        IndependentDevelopmentEvidenceTargets target record then
      some {
        record := record,
        certificate := {
          certificate := certificate,
          metadataAccepted := hMeta,
          sameStatement := sameStatement
        },
        targetAccepted := hTarget
      }
    else
      none
  else
    none

theorem verifyIndependentDevelopmentEvidence_some_sound
    {target : ProvenanceTarget}
    {record : IndependentDevelopmentEvidenceRecord}
    {certificate : CertifiedProvenanceClaim}
    {sameStatement :
      certificate.statement =
        (independentDevelopmentEvidenceQuery record).statement}
    {verified : VerifiedIndependentDevelopmentEvidence target}
    (_h :
      verifyIndependentDevelopmentEvidence? target record certificate
        sameStatement = some verified) :
    IndependentDevelopmentWithinDeclaredUniverse
      target verified.record := by
  exact And.intro
    (VerifiedCertificateFor.provesQuery verified.certificate)
    verified.targetAccepted

inductive ProvenanceAssertionKind where
  | exclusivePrimary (assertedOrigin : AgentId)
  | authorizedDerivative
      (assertedOrigin : AgentId)
      (authorizedSubject : AgentId)
  | independentDevelopment
      (assertedSubject : AgentId)
deriving DecidableEq

structure ProvenanceAssertionRecord where
  target : ProvenanceTarget
  assertionId : String
  issuerId : IssuerId
  assertionKind : ProvenanceAssertionKind
deriving DecidableEq

def AssertionRecordWithinTarget
    (target : ProvenanceTarget)
    (record : ProvenanceAssertionRecord) : Prop :=
  record.target = target

instance
    (target : ProvenanceTarget)
    (record : ProvenanceAssertionRecord) :
    Decidable (AssertionRecordWithinTarget target record) := by
  unfold AssertionRecordWithinTarget
  infer_instance

def ProvenanceAssertionInternallyValid
    (record : ProvenanceAssertionRecord) : Prop :=
  Not (record.assertionId = "")

instance (record : ProvenanceAssertionRecord) :
    Decidable (ProvenanceAssertionInternallyValid record) := by
  unfold ProvenanceAssertionInternallyValid
  infer_instance

def assertionEvidenceQuery
    (record : ProvenanceAssertionRecord) : ProvenanceQuery :=
  {
    claimId := record.target.claimId,
    specificationId := record.target.specificationId,
    specificationVersion := record.target.specificationVersion,
    artifactDigest := record.target.artifactDigest,
    subjectAgentId := record.target.subjectAgentId,
    issuerId := record.issuerId,
    statement := ProvenanceAssertionInternallyValid record
  }

structure VerifiedProvenanceAssertion
    (target : ProvenanceTarget) where
  record : ProvenanceAssertionRecord
  certificate :
    VerifiedCertificateFor ProvenanceCertificateKind.conflict
      (assertionEvidenceQuery record)
  targetAccepted : AssertionRecordWithinTarget target record

def verifyProvenanceAssertion?
    (target : ProvenanceTarget)
    (record : ProvenanceAssertionRecord)
    (certificate : CertifiedProvenanceClaim)
    (sameStatement :
      certificate.statement =
        (assertionEvidenceQuery record).statement) :
    Option (VerifiedProvenanceAssertion target) :=
  if hMeta :
      verifyCertificateMetadata ProvenanceCertificateKind.conflict
        (assertionEvidenceQuery record) certificate = true then
    if hTarget : AssertionRecordWithinTarget target record then
      some {
        record := record,
        certificate := {
          certificate := certificate,
          metadataAccepted := hMeta,
          sameStatement := sameStatement
        },
        targetAccepted := hTarget
      }
    else
      none
  else
    none

def mutuallyExclusiveAssertionsBool
    (left right : ProvenanceAssertionRecord) : Bool :=
  decide (left.target = right.target) &&
  decide (Not (left.assertionId = right.assertionId)) &&
  match left.assertionKind, right.assertionKind with
  | ProvenanceAssertionKind.exclusivePrimary originLeft,
      ProvenanceAssertionKind.exclusivePrimary originRight =>
      decide (Not (originLeft = originRight))
  | _, _ => false

def MutuallyExclusiveAssertions
    (left right : ProvenanceAssertionRecord) : Prop :=
  mutuallyExclusiveAssertionsBool left right = true

instance
    (left right : ProvenanceAssertionRecord) :
    Decidable (MutuallyExclusiveAssertions left right) := by
  unfold MutuallyExclusiveAssertions
  infer_instance

structure VerifiedConflictEvidence
    (target : ProvenanceTarget) where
  left : VerifiedProvenanceAssertion target
  right : VerifiedProvenanceAssertion target
  exclusive :
    MutuallyExclusiveAssertions left.record right.record

def verifyConflictEvidence?
    (target : ProvenanceTarget)
    (leftRecord : ProvenanceAssertionRecord)
    (leftCertificate : CertifiedProvenanceClaim)
    (leftSameStatement :
      leftCertificate.statement =
        (assertionEvidenceQuery leftRecord).statement)
    (rightRecord : ProvenanceAssertionRecord)
    (rightCertificate : CertifiedProvenanceClaim)
    (rightSameStatement :
      rightCertificate.statement =
        (assertionEvidenceQuery rightRecord).statement) :
    Option (VerifiedConflictEvidence target) :=
  match
      verifyProvenanceAssertion? target leftRecord leftCertificate
        leftSameStatement,
      verifyProvenanceAssertion? target rightRecord rightCertificate
        rightSameStatement with
  | some leftVerified, some rightVerified =>
      if hExclusive :
          MutuallyExclusiveAssertions leftVerified.record
            rightVerified.record then
        some {
          left := leftVerified,
          right := rightVerified,
          exclusive := hExclusive
        }
      else
        none
  | _, _ => none

theorem verifyConflictEvidence_some_sound
    {target : ProvenanceTarget}
    {leftRecord : ProvenanceAssertionRecord}
    {leftCertificate : CertifiedProvenanceClaim}
    {leftSameStatement :
      leftCertificate.statement =
        (assertionEvidenceQuery leftRecord).statement}
    {rightRecord : ProvenanceAssertionRecord}
    {rightCertificate : CertifiedProvenanceClaim}
    {rightSameStatement :
      rightCertificate.statement =
        (assertionEvidenceQuery rightRecord).statement}
    {verified : VerifiedConflictEvidence target}
    (_h :
      verifyConflictEvidence? target leftRecord leftCertificate
        leftSameStatement rightRecord rightCertificate
        rightSameStatement = some verified) :
    MutuallyExclusiveAssertions
      verified.left.record verified.right.record := by
  exact verified.exclusive

/-! ## 3. Verified evidence bundles and provenance status -/

structure VerifiedProvenanceEvidenceBundle
    (target : ProvenanceTarget) where
  primary : Option (VerifiedPrimaryEvidence target)
  authorization : Option (VerifiedAuthorizationEvidence target)
  independentDevelopment :
    Option (VerifiedIndependentDevelopmentEvidence target)
  conflict : Option (VerifiedConflictEvidence target)

inductive ProvenanceStatus where
  | clear
  | unresolved
  | conflicted
deriving DecidableEq

def provenanceStatus
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) :
    ProvenanceStatus :=
  match bundle.conflict with
  | some _ => ProvenanceStatus.conflicted
  | none =>
      match bundle.primary, bundle.authorization,
          bundle.independentDevelopment with
      | none, none, none => ProvenanceStatus.unresolved
      | _, _, _ => ProvenanceStatus.clear

def HasVerifiedPrimaryEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  exists evidence, bundle.primary = some evidence

def HasVerifiedAuthorizationEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  exists evidence, bundle.authorization = some evidence

def HasVerifiedIndependentDevelopmentEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  exists evidence, bundle.independentDevelopment = some evidence

def HasVerifiedConflictEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  exists evidence, bundle.conflict = some evidence

def HasVerifiedClearanceEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  HasVerifiedPrimaryEvidence bundle \/
  HasVerifiedAuthorizationEvidence bundle \/
  HasVerifiedIndependentDevelopmentEvidence bundle

def NoVerifiedConflictEvidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target) : Prop :=
  bundle.conflict = none

theorem option_eq_none_of_no_some
    {alpha : Type u}
    {value : Option alpha}
    (h : Not (exists item, value = some item)) :
    value = none := by
  cases value with
  | none => rfl
  | some item =>
      exact False.elim (h (Exists.intro item rfl))

theorem verified_conflict_takes_precedence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hConflict : HasVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.conflicted := by
  obtain ⟨evidence, hEvidence⟩ := hConflict
  unfold provenanceStatus
  rw [hEvidence]

theorem verified_primary_without_conflict_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hPrimary : HasVerifiedPrimaryEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear := by
  obtain ⟨evidence, hEvidence⟩ := hPrimary
  unfold provenanceStatus
  rw [hNoConflict, hEvidence]

theorem verified_authorization_without_conflict_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hAuthorization : HasVerifiedAuthorizationEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear := by
  obtain ⟨evidence, hEvidence⟩ := hAuthorization
  unfold provenanceStatus
  rw [hNoConflict, hEvidence]
  cases bundle.primary <;> rfl

theorem verified_independent_without_conflict_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hIndependent :
      HasVerifiedIndependentDevelopmentEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear := by
  obtain ⟨evidence, hEvidence⟩ := hIndependent
  unfold provenanceStatus
  rw [hNoConflict, hEvidence]
  cases bundle.primary <;> cases bundle.authorization <;> rfl

theorem valid_primary_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hPrimary : HasVerifiedPrimaryEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear :=
  verified_primary_without_conflict_is_clear
    bundle hPrimary hNoConflict

theorem valid_authorized_derivative_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hAuthorization : HasVerifiedAuthorizationEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear :=
  verified_authorization_without_conflict_is_clear
    bundle hAuthorization hNoConflict

theorem valid_independent_development_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hIndependent :
      HasVerifiedIndependentDevelopmentEvidence bundle)
    (hNoConflict : NoVerifiedConflictEvidence bundle) :
    provenanceStatus bundle = ProvenanceStatus.clear :=
  verified_independent_without_conflict_is_clear
    bundle hIndependent hNoConflict

theorem no_verified_evidence_is_unresolved
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hNoClearance : Not (HasVerifiedClearanceEvidence bundle))
    (hNoConflict : Not (HasVerifiedConflictEvidence bundle)) :
    provenanceStatus bundle = ProvenanceStatus.unresolved := by
  have hNoPrimary :
      Not (HasVerifiedPrimaryEvidence bundle) := by
    intro hPrimary
    exact hNoClearance (Or.inl hPrimary)
  have hNoAuthorization :
      Not (HasVerifiedAuthorizationEvidence bundle) := by
    intro hAuthorization
    exact hNoClearance (Or.inr (Or.inl hAuthorization))
  have hNoIndependent :
      Not (HasVerifiedIndependentDevelopmentEvidence bundle) := by
    intro hIndependent
    exact hNoClearance (Or.inr (Or.inr hIndependent))
  have hPrimaryNone := option_eq_none_of_no_some hNoPrimary
  have hAuthorizationNone :=
    option_eq_none_of_no_some hNoAuthorization
  have hIndependentNone :=
    option_eq_none_of_no_some hNoIndependent
  have hConflictNone := option_eq_none_of_no_some hNoConflict
  unfold provenanceStatus
  rw [hConflictNone, hPrimaryNone, hAuthorizationNone,
    hIndependentNone]

theorem clear_status_has_verified_clearance_evidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (h : provenanceStatus bundle = ProvenanceStatus.clear) :
    HasVerifiedClearanceEvidence bundle := by
  cases bundle with
  | mk primary authorization independent conflict =>
      cases conflict with
      | some conflictEvidence =>
          unfold provenanceStatus at h
          cases h
      | none =>
          cases primary with
          | some primaryEvidence =>
              exact Or.inl (Exists.intro primaryEvidence rfl)
          | none =>
              cases authorization with
              | some authorizationEvidence =>
                  exact Or.inr
                    (Or.inl
                      (Exists.intro authorizationEvidence rfl))
              | none =>
                  cases independent with
                  | some independentEvidence =>
                      exact Or.inr
                        (Or.inr
                          (Exists.intro independentEvidence rfl))
                  | none =>
                      unfold provenanceStatus at h
                      cases h

theorem conflicted_status_has_verified_conflict_evidence
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (h :
      provenanceStatus bundle = ProvenanceStatus.conflicted) :
    HasVerifiedConflictEvidence bundle := by
  cases bundle with
  | mk primary authorization independent conflict =>
      cases conflict with
      | some conflictEvidence =>
          exact Exists.intro conflictEvidence rfl
      | none =>
          unfold provenanceStatus at h
          cases primary <;> cases authorization <;>
            cases independent <;> cases h

theorem unresolved_status_has_no_verified_clearance_or_conflict
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (h :
      provenanceStatus bundle = ProvenanceStatus.unresolved) :
    Not (HasVerifiedClearanceEvidence bundle) /\
    Not (HasVerifiedConflictEvidence bundle) := by
  have hNoConflict :
      Not (HasVerifiedConflictEvidence bundle) := by
    intro hConflict
    have hStatus :=
      verified_conflict_takes_precedence bundle hConflict
    rw [hStatus] at h
    cases h
  have hConflictNone := option_eq_none_of_no_some hNoConflict
  constructor
  · intro hClearance
    have hClear :
        provenanceStatus bundle = ProvenanceStatus.clear := by
      cases hClearance with
      | inl hPrimary =>
          exact verified_primary_without_conflict_is_clear
            bundle hPrimary hConflictNone
      | inr hRest =>
          cases hRest with
          | inl hAuthorization =>
              exact verified_authorization_without_conflict_is_clear
                bundle hAuthorization hConflictNone
          | inr hIndependent =>
              exact verified_independent_without_conflict_is_clear
                bundle hIndependent hConflictNone
    rw [hClear] at h
    cases h
  · exact hNoConflict

theorem no_verified_clearance_cannot_be_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (hNoClearance : Not (HasVerifiedClearanceEvidence bundle)) :
    Not (provenanceStatus bundle = ProvenanceStatus.clear) := by
  intro hClear
  exact hNoClearance
    (clear_status_has_verified_clearance_evidence bundle hClear)

def emptyEvidenceBundle
    (target : ProvenanceTarget) :
    VerifiedProvenanceEvidenceBundle target :=
  {
    primary := none,
    authorization := none,
    independentDevelopment := none,
    conflict := none
  }

/-! ## 4. Market signals are separated from verified evidence -/

structure MarketSignals where
  authority : Nat
  popularity : Nat
  adoptionCount : Nat
deriving DecidableEq

structure ProvenanceAssessment where
  target : ProvenanceTarget
  evidence : VerifiedProvenanceEvidenceBundle target

structure ProvenanceRecord where
  provenance : ProvenanceAssessment
  signals : MarketSignals

def assessmentStatus
    (assessment : ProvenanceAssessment) : ProvenanceStatus :=
  provenanceStatus assessment.evidence

def recordStatus (record : ProvenanceRecord) : ProvenanceStatus :=
  assessmentStatus record.provenance

def replaceMarketSignals
    (record : ProvenanceRecord)
    (signals : MarketSignals) : ProvenanceRecord :=
  { record with signals := signals }

def withPopularity
    (record : ProvenanceRecord)
    (newPopularity : Nat) : ProvenanceRecord :=
  replaceMarketSignals record
    { record.signals with popularity := newPopularity }

def withAuthority
    (record : ProvenanceRecord)
    (newAuthority : Nat) : ProvenanceRecord :=
  replaceMarketSignals record
    { record.signals with authority := newAuthority }

def withAdoptionCount
    (record : ProvenanceRecord)
    (newAdoptionCount : Nat) : ProvenanceRecord :=
  replaceMarketSignals record
    { record.signals with adoptionCount := newAdoptionCount }

theorem provenance_status_invariant_under_market_signals
    (assessment : ProvenanceAssessment)
    (before after : MarketSignals) :
    recordStatus { provenance := assessment, signals := before } =
      recordStatus { provenance := assessment, signals := after } := by
  rfl

theorem market_signal_replacement_keeps_provenance_status
    (record : ProvenanceRecord)
    (signals : MarketSignals) :
    recordStatus (replaceMarketSignals record signals) =
      recordStatus record := by
  cases record
  rfl

theorem popularity_cannot_clear_unresolved_provenance
    (record : ProvenanceRecord)
    (newPopularity : Nat)
    (hUnresolved : recordStatus record = ProvenanceStatus.unresolved) :
    recordStatus (withPopularity record newPopularity) =
      ProvenanceStatus.unresolved := by
  cases record
  exact hUnresolved

theorem popularity_cannot_create_conflict
    (record : ProvenanceRecord)
    (newPopularity : Nat)
    (hNotConflicted :
      Not (recordStatus record = ProvenanceStatus.conflicted)) :
    Not (recordStatus (withPopularity record newPopularity) =
      ProvenanceStatus.conflicted) := by
  intro hConflict
  apply hNotConflicted
  cases record
  exact hConflict

theorem authority_does_not_change_provenance_status
    (record : ProvenanceRecord)
    (newAuthority : Nat) :
    recordStatus (withAuthority record newAuthority) =
      recordStatus record := by
  cases record
  rfl

theorem adoption_count_does_not_change_provenance_status
    (record : ProvenanceRecord)
    (newAdoptionCount : Nat) :
    recordStatus (withAdoptionCount record newAdoptionCount) =
      recordStatus record := by
  cases record
  rfl

/-! ## 5. Scoped adoption findings and policy -/

structure AdoptionScope where
  adopter : AgentId
  artifact : ArtifactId
  useContext : UseContextId
  claim : ClaimId
deriving DecidableEq

def RelatedScope (left right : AdoptionScope) : Prop :=
  left.adopter = right.adopter /\
  left.artifact = right.artifact /\
  left.useContext = right.useContext /\
  left.claim = right.claim

instance (left right : AdoptionScope) :
    Decidable (RelatedScope left right) := by
  unfold RelatedScope
  infer_instance

inductive AdoptionDisposition where
  | adopt
  | adoptWithDisclosure
  | review
  | hold
  | reject
deriving DecidableEq

def frictionRank : AdoptionDisposition -> Nat
  | AdoptionDisposition.adopt => 0
  | AdoptionDisposition.adoptWithDisclosure => 1
  | AdoptionDisposition.review => 2
  | AdoptionDisposition.hold => 3
  | AdoptionDisposition.reject => 4

theorem friction_positive_of_not_adopt
    (disposition : AdoptionDisposition)
    (hNotAdopt :
      Not (disposition = AdoptionDisposition.adopt)) :
    0 < frictionRank disposition := by
  cases disposition with
  | adopt =>
      exact False.elim (hNotAdopt rfl)
  | adoptWithDisclosure =>
      unfold frictionRank
      exact Nat.zero_lt_succ 0
  | review =>
      unfold frictionRank
      exact Nat.zero_lt_succ 1
  | hold =>
      unfold frictionRank
      exact Nat.zero_lt_succ 2
  | reject =>
      unfold frictionRank
      exact Nat.zero_lt_succ 3

def RequiresReviewOrHold
    (disposition : AdoptionDisposition) : Prop :=
  disposition = AdoptionDisposition.review \/
    disposition = AdoptionDisposition.hold

structure ScopedFinding where
  scope : AdoptionScope
  status : ProvenanceStatus
  disposition : AdoptionDisposition
deriving DecidableEq

def FindingRequiresReviewOrHold
    (finding : ScopedFinding) : Prop :=
  RequiresReviewOrHold finding.disposition

def ReviewPropagatesTo
    (finding : ScopedFinding)
    (target : AdoptionScope) : Prop :=
  RelatedScope finding.scope target /\
    FindingRequiresReviewOrHold finding

theorem scoped_review_does_not_propagate_to_unrelated_scope
    (finding : ScopedFinding)
    (target : AdoptionScope)
    (hUnrelated : Not (RelatedScope finding.scope target)) :
    Not (ReviewPropagatesTo finding target) := by
  intro hPropagates
  exact hUnrelated hPropagates.left

structure Candidate where
  provenance : ProvenanceAssessment
  signals : MarketSignals
  functionalFit : Bool
  nonProvenanceMerit : Nat
  mitigation : Bool

structure AdoptionContext where
  adopter : AgentId
  useContext : UseContextId
  claim : ClaimId
  relevant : Bool
  material : Bool
  highResponsibility : Bool
  minNonProvenanceMerit : Nat
deriving DecidableEq

def candidateArtifactId (candidate : Candidate) : ArtifactId :=
  candidate.provenance.target.artifactId

def CandidateProvenanceBound (candidate : Candidate) : Prop :=
  candidateArtifactId candidate =
    candidate.provenance.target.artifactId

instance (candidate : Candidate) :
    Decidable (CandidateProvenanceBound candidate) := by
  unfold CandidateProvenanceBound candidateArtifactId
  infer_instance

theorem candidate_provenance_bound_by_construction
    (candidate : Candidate) :
    CandidateProvenanceBound candidate := by
  rfl

def ContextMatchesCandidate
    (candidate : Candidate)
    (context : AdoptionContext) : Prop :=
  context.claim =
    candidate.provenance.target.claimId

instance (candidate : Candidate) (context : AdoptionContext) :
    Decidable (ContextMatchesCandidate candidate context) := by
  unfold ContextMatchesCandidate
  infer_instance

def candidateStatus (candidate : Candidate) : ProvenanceStatus :=
  assessmentStatus candidate.provenance

def candidateScope
    (candidate : Candidate)
    (context : AdoptionContext) : AdoptionScope :=
  {
    adopter := context.adopter,
    artifact := candidate.provenance.target.artifactId,
    useContext := context.useContext,
    claim := candidate.provenance.target.claimId
  }

def nonProvenancePassBool
    (candidate : Candidate)
    (context : AdoptionContext) : Bool :=
  decide
    (context.minNonProvenanceMerit <=
      candidate.nonProvenanceMerit)

def NonProvenancePass
    (candidate : Candidate)
    (context : AdoptionContext) : Prop :=
  context.minNonProvenanceMerit <=
    candidate.nonProvenanceMerit

instance (candidate : Candidate) (context : AdoptionContext) :
    Decidable (NonProvenancePass candidate context) := by
  unfold NonProvenancePass
  infer_instance

theorem nonProvenancePassBool_of_pass
    (candidate : Candidate)
    (context : AdoptionContext)
    (hPass : NonProvenancePass candidate context) :
    nonProvenancePassBool candidate context = true := by
  unfold nonProvenancePassBool NonProvenancePass at *
  exact decide_eq_true hPass

theorem nonProvenancePassBool_not_true_of_not_pass
    (candidate : Candidate)
    (context : AdoptionContext)
    (hNotPass :
      Not (NonProvenancePass candidate context)) :
    Not (nonProvenancePassBool candidate context = true) := by
  intro hBool
  apply hNotPass
  unfold nonProvenancePassBool at hBool
  unfold NonProvenancePass
  exact of_decide_eq_true hBool

def NonProvenanceNotWorse
    (better weaker : Candidate) : Prop :=
  weaker.nonProvenanceMerit <= better.nonProvenanceMerit

instance (better weaker : Candidate) :
    Decidable (NonProvenanceNotWorse better weaker) := by
  unfold NonProvenanceNotWorse
  infer_instance

def unmitigatedMaterialGate
    (candidate : Candidate)
    (context : AdoptionContext) : Bool :=
  context.relevant && context.material && Bool.not candidate.mitigation

def responsibleDecision
    (candidate : Candidate)
    (context : AdoptionContext) : AdoptionDisposition :=
  if CandidateProvenanceBound candidate then
    if ContextMatchesCandidate candidate context then
      if candidate.functionalFit then
        if nonProvenancePassBool candidate context then
          match candidateStatus candidate with
          | ProvenanceStatus.clear =>
              AdoptionDisposition.adopt
          | ProvenanceStatus.conflicted =>
              AdoptionDisposition.hold
          | ProvenanceStatus.unresolved =>
              if unmitigatedMaterialGate candidate context then
                if context.highResponsibility then
                  AdoptionDisposition.hold
                else
                  AdoptionDisposition.review
              else
                AdoptionDisposition.adoptWithDisclosure
        else
          AdoptionDisposition.reject
      else
        AdoptionDisposition.reject
    else
      AdoptionDisposition.reject
  else
    AdoptionDisposition.reject

def scopedFinding?
    (candidate : Candidate)
    (context : AdoptionContext) : Option ScopedFinding :=
  if CandidateProvenanceBound candidate then
    if ContextMatchesCandidate candidate context then
      if candidate.functionalFit then
        if nonProvenancePassBool candidate context then
          match candidateStatus candidate with
          | ProvenanceStatus.clear =>
              none
          | ProvenanceStatus.conflicted =>
              some {
                scope := candidateScope candidate context,
                status := ProvenanceStatus.conflicted,
                disposition := AdoptionDisposition.hold
              }
          | ProvenanceStatus.unresolved =>
              if unmitigatedMaterialGate candidate context then
                if context.highResponsibility then
                  some {
                    scope := candidateScope candidate context,
                    status := ProvenanceStatus.unresolved,
                    disposition := AdoptionDisposition.hold
                  }
                else
                  some {
                    scope := candidateScope candidate context,
                    status := ProvenanceStatus.unresolved,
                    disposition := AdoptionDisposition.review
                  }
              else
                none
        else
          none
      else
        none
    else
      none
  else
    none

theorem responsibleDecision_unfit_not_adopt
    (candidate : Candidate)
    (context : AdoptionContext)
    (hFit : candidate.functionalFit = false) :
    Not (responsibleDecision candidate context =
      AdoptionDisposition.adopt) := by
  have hFitNot : Not (candidate.functionalFit = true) := by
    intro h
    rw [hFit] at h
    cases h
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  by_cases hContext : ContextMatchesCandidate candidate context
  · rw [if_pos hContext]
    rw [if_neg hFitNot]
    intro h
    cases h
  · rw [if_neg hContext]
    intro h
    cases h

theorem responsibleDecision_context_mismatch_rejects
    (candidate : Candidate)
    (context : AdoptionContext)
    (hMismatch :
      Not (ContextMatchesCandidate candidate context)) :
    responsibleDecision candidate context =
      AdoptionDisposition.reject := by
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  rw [if_neg hMismatch]

theorem scopedFinding_context_mismatch_none
    (candidate : Candidate)
    (context : AdoptionContext)
    (hMismatch :
      Not (ContextMatchesCandidate candidate context)) :
    scopedFinding? candidate context = none := by
  unfold scopedFinding?
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  rw [if_neg hMismatch]

theorem responsibleDecision_non_provenance_failure_not_adopt
    (candidate : Candidate)
    (context : AdoptionContext)
    (hFit : candidate.functionalFit = true)
    (hScore : Not (NonProvenancePass candidate context)) :
    Not (responsibleDecision candidate context =
      AdoptionDisposition.adopt) := by
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  by_cases hContext : ContextMatchesCandidate candidate context
  · rw [if_pos hContext]
    rw [if_pos hFit]
    rw [if_neg (nonProvenancePassBool_not_true_of_not_pass
      candidate context hScore)]
    intro h
    cases h
  · rw [if_neg hContext]
    intro h
    cases h

theorem responsibleDecision_clear_fit_pass_adopts
    (candidate : Candidate)
    (context : AdoptionContext)
    (hContext : ContextMatchesCandidate candidate context)
    (hFit : candidate.functionalFit = true)
    (hScore : NonProvenancePass candidate context)
    (hStatus : candidateStatus candidate = ProvenanceStatus.clear) :
    responsibleDecision candidate context =
      AdoptionDisposition.adopt := by
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  rw [if_pos hContext]
  rw [if_pos hFit]
  rw [if_pos (nonProvenancePassBool_of_pass
    candidate context hScore)]
  rw [hStatus]

theorem responsibleDecision_unresolved_material_not_adopt
    (candidate : Candidate)
    (context : AdoptionContext)
    (hFit : candidate.functionalFit = true)
    (hScore : NonProvenancePass candidate context)
    (hRelevant : context.relevant = true)
    (hMaterial : context.material = true)
    (hNoMitigation : candidate.mitigation = false)
    (hStatus :
      candidateStatus candidate = ProvenanceStatus.unresolved) :
    Not (responsibleDecision candidate context =
      AdoptionDisposition.adopt) := by
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  by_cases hContext : ContextMatchesCandidate candidate context
  · rw [if_pos hContext]
    rw [if_pos hFit]
    rw [if_pos (nonProvenancePassBool_of_pass
      candidate context hScore)]
    rw [hStatus]
    have hGate :
        unmitigatedMaterialGate candidate context = true := by
      unfold unmitigatedMaterialGate
      rw [hRelevant, hMaterial, hNoMitigation]
      rfl
    rw [if_pos hGate]
    cases context.highResponsibility <;> decide
  · rw [if_neg hContext]
    intro h
    cases h

theorem responsibleDecision_conflicted_not_adopt
    (candidate : Candidate)
    (context : AdoptionContext)
    (hFit : candidate.functionalFit = true)
    (hScore : NonProvenancePass candidate context)
    (hStatus :
      candidateStatus candidate = ProvenanceStatus.conflicted) :
    Not (responsibleDecision candidate context =
      AdoptionDisposition.adopt) := by
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  by_cases hContext : ContextMatchesCandidate candidate context
  · rw [if_pos hContext]
    rw [if_pos hFit]
    rw [if_pos (nonProvenancePassBool_of_pass
      candidate context hScore)]
    rw [hStatus]
    intro h
    cases h
  · rw [if_neg hContext]
    intro h
    cases h

inductive VerifiedResolutionEvidence
    (target : ProvenanceTarget) where
  | authorization
      (evidence : VerifiedAuthorizationEvidence target)
  | independentDevelopment
      (evidence : VerifiedIndependentDevelopmentEvidence target)

def addVerifiedResolution
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (resolution : VerifiedResolutionEvidence target) :
    VerifiedProvenanceEvidenceBundle target :=
  match resolution with
  | VerifiedResolutionEvidence.authorization evidence =>
      { bundle with authorization := some evidence }
  | VerifiedResolutionEvidence.independentDevelopment evidence =>
      { bundle with independentDevelopment := some evidence }

def replaceCandidateEvidence
    (candidate : Candidate)
    (evidence :
      VerifiedProvenanceEvidenceBundle candidate.provenance.target) :
    Candidate :=
  {
    provenance := {
      target := candidate.provenance.target,
      evidence := evidence
    },
    signals := candidate.signals,
    functionalFit := candidate.functionalFit,
    nonProvenanceMerit := candidate.nonProvenanceMerit,
    mitigation := candidate.mitigation
  }

def addResolutionToCandidate
    (candidate : Candidate)
    (resolution :
      VerifiedResolutionEvidence candidate.provenance.target) :
    Candidate :=
  replaceCandidateEvidence candidate
    (addVerifiedResolution candidate.provenance.evidence resolution)

theorem add_verified_resolution_is_clear
    {target : ProvenanceTarget}
    (bundle : VerifiedProvenanceEvidenceBundle target)
    (resolution : VerifiedResolutionEvidence target)
    (hOld :
      provenanceStatus bundle = ProvenanceStatus.unresolved) :
    provenanceStatus (addVerifiedResolution bundle resolution) =
      ProvenanceStatus.clear := by
  have hNoConflict :=
    (unresolved_status_has_no_verified_clearance_or_conflict
      bundle hOld).right
  have hConflictNone := option_eq_none_of_no_some hNoConflict
  cases resolution with
  | authorization authorizationEvidence =>
      exact verified_authorization_without_conflict_is_clear
        (addVerifiedResolution bundle
          (VerifiedResolutionEvidence.authorization
            authorizationEvidence))
        (Exists.intro authorizationEvidence rfl)
        (by
          unfold NoVerifiedConflictEvidence addVerifiedResolution
          exact hConflictNone)
  | independentDevelopment independentEvidence =>
      exact verified_independent_without_conflict_is_clear
        (addVerifiedResolution bundle
          (VerifiedResolutionEvidence.independentDevelopment
            independentEvidence))
        (Exists.intro independentEvidence rfl)
        (by
          unfold NoVerifiedConflictEvidence addVerifiedResolution
          exact hConflictNone)

structure ResponsibleAdoptionPolicy where
  decide : Candidate -> AdoptionContext -> AdoptionDisposition
  contextMismatchNotAdopt :
    forall candidate context,
      Not (ContextMatchesCandidate candidate context) ->
      Not (decide candidate context = AdoptionDisposition.adopt)
  unfitNotAdopt :
    forall candidate context,
      candidate.functionalFit = false ->
      Not (decide candidate context = AdoptionDisposition.adopt)
  nonProvenanceFailureNotAdopt :
    forall candidate context,
      candidate.functionalFit = true ->
      Not (NonProvenancePass candidate context) ->
      Not (decide candidate context = AdoptionDisposition.adopt)
  clearFitPassAdopts :
    forall candidate context,
      ContextMatchesCandidate candidate context ->
      candidate.functionalFit = true ->
      NonProvenancePass candidate context ->
      candidateStatus candidate = ProvenanceStatus.clear ->
      decide candidate context = AdoptionDisposition.adopt
  unresolvedMaterialUseNotAdopt :
    forall candidate context,
      candidate.functionalFit = true ->
      NonProvenancePass candidate context ->
      context.relevant = true ->
      context.material = true ->
      candidate.mitigation = false ->
      candidateStatus candidate = ProvenanceStatus.unresolved ->
      Not (decide candidate context = AdoptionDisposition.adopt)
  conflictedNotAdopt :
    forall candidate context,
      candidate.functionalFit = true ->
      NonProvenancePass candidate context ->
      candidateStatus candidate = ProvenanceStatus.conflicted ->
      Not (decide candidate context = AdoptionDisposition.adopt)
  scopeLimited :
    forall finding target,
      Not (RelatedScope finding.scope target) ->
      Not (ReviewPropagatesTo finding target)
  redecideAfterResolution :
    forall candidate context resolution,
      ContextMatchesCandidate candidate context ->
      candidate.functionalFit = true ->
      NonProvenancePass candidate context ->
      candidateStatus candidate = ProvenanceStatus.unresolved ->
      decide (addResolutionToCandidate candidate resolution)
        context = AdoptionDisposition.adopt
  marketSignalsDoNotChangeStatus :
    forall assessment before after,
      recordStatus { provenance := assessment, signals := before } =
        recordStatus { provenance := assessment, signals := after }

def responsiblePolicy : ResponsibleAdoptionPolicy where
  decide := responsibleDecision
  contextMismatchNotAdopt := by
    intro candidate context hMismatch
    rw [responsibleDecision_context_mismatch_rejects
      candidate context hMismatch]
    intro h
    cases h
  unfitNotAdopt := responsibleDecision_unfit_not_adopt
  nonProvenanceFailureNotAdopt :=
    responsibleDecision_non_provenance_failure_not_adopt
  clearFitPassAdopts := responsibleDecision_clear_fit_pass_adopts
  unresolvedMaterialUseNotAdopt :=
    responsibleDecision_unresolved_material_not_adopt
  conflictedNotAdopt := responsibleDecision_conflicted_not_adopt
  scopeLimited := scoped_review_does_not_propagate_to_unrelated_scope
  redecideAfterResolution := by
    intro candidate context resolution hContext hFit hScore hOld
    exact responsibleDecision_clear_fit_pass_adopts
      (addResolutionToCandidate candidate resolution)
      context
      (by
        unfold ContextMatchesCandidate addResolutionToCandidate
          replaceCandidateEvidence at *
        exact hContext)
      (by exact hFit)
      (by
        unfold addResolutionToCandidate replaceCandidateEvidence
          NonProvenancePass at *
        exact hScore)
      (by
        unfold candidateStatus assessmentStatus
          addResolutionToCandidate replaceCandidateEvidence
        exact add_verified_resolution_is_clear
          candidate.provenance.evidence resolution hOld)
  marketSignalsDoNotChangeStatus :=
    provenance_status_invariant_under_market_signals

theorem unresolved_material_use_requires_scoped_review
    (candidate : Candidate)
    (context : AdoptionContext)
    (hContext : ContextMatchesCandidate candidate context)
    (hFit : candidate.functionalFit = true)
    (hScore : NonProvenancePass candidate context)
    (hRelevant : context.relevant = true)
    (hMaterial : context.material = true)
    (hNoMitigation : candidate.mitigation = false)
    (hStatus :
      candidateStatus candidate = ProvenanceStatus.unresolved) :
    RequiresReviewOrHold
      (responsiblePolicy.decide candidate context) := by
  change RequiresReviewOrHold
    (responsibleDecision candidate context)
  unfold responsibleDecision
  rw [if_pos (candidate_provenance_bound_by_construction candidate)]
  rw [if_pos hContext]
  rw [if_pos hFit]
  rw [if_pos (nonProvenancePassBool_of_pass
    candidate context hScore)]
  rw [hStatus]
  have hGate :
      unmitigatedMaterialGate candidate context = true := by
    unfold unmitigatedMaterialGate
    rw [hRelevant, hMaterial, hNoMitigation]
    rfl
  rw [if_pos hGate]
  unfold RequiresReviewOrHold
  cases context.highResponsibility <;> decide

theorem valid_resolution_clears_scoped_review
    (candidate : Candidate)
    (context : AdoptionContext)
    (resolution :
      VerifiedResolutionEvidence candidate.provenance.target)
    (hOld :
      candidateStatus candidate = ProvenanceStatus.unresolved)
    (hContext : ContextMatchesCandidate candidate context)
    (hFit : candidate.functionalFit = true)
    (hScore : NonProvenancePass candidate context) :
    responsiblePolicy.decide
        (addResolutionToCandidate candidate resolution) context =
      AdoptionDisposition.adopt /\
    scopedFinding?
        (addResolutionToCandidate candidate resolution) context =
      none := by
  have hClear :
      candidateStatus
          (addResolutionToCandidate candidate resolution) =
        ProvenanceStatus.clear := by
    unfold candidateStatus assessmentStatus addResolutionToCandidate
      replaceCandidateEvidence
    exact add_verified_resolution_is_clear
      candidate.provenance.evidence resolution hOld
  have hDecision :
      responsibleDecision
          (addResolutionToCandidate candidate resolution) context =
        AdoptionDisposition.adopt :=
    responsibleDecision_clear_fit_pass_adopts
      (addResolutionToCandidate candidate resolution)
      context
      (by
        unfold ContextMatchesCandidate addResolutionToCandidate
          replaceCandidateEvidence at *
        exact hContext)
      (by exact hFit)
      (by
        unfold addResolutionToCandidate replaceCandidateEvidence
          NonProvenancePass at *
        exact hScore)
      hClear
  constructor
  · change
      responsibleDecision
          (addResolutionToCandidate candidate resolution) context =
        AdoptionDisposition.adopt
    exact hDecision
  · unfold scopedFinding?
    rw [if_pos
      (candidate_provenance_bound_by_construction
        (addResolutionToCandidate candidate resolution))]
    rw [if_pos (by
      unfold ContextMatchesCandidate addResolutionToCandidate
        replaceCandidateEvidence at *
      exact hContext)]
    rw [if_pos (by exact hFit)]
    rw [if_pos (nonProvenancePassBool_of_pass
      (addResolutionToCandidate candidate resolution)
      context
      (by
        unfold addResolutionToCandidate replaceCandidateEvidence
          NonProvenancePass at *
        exact hScore))]
    rw [hClear]

theorem verified_provenance_adoption_friction_dominance
    (policy : ResponsibleAdoptionPolicy)
    (clearCandidate unresolvedCandidate : Candidate)
    (context : AdoptionContext)
    (hClearContext :
      ContextMatchesCandidate clearCandidate context)
    (_hUnresolvedContext :
      ContextMatchesCandidate unresolvedCandidate context)
    (hClearFit : clearCandidate.functionalFit = true)
    (hUnresolvedFit : unresolvedCandidate.functionalFit = true)
    (hUnresolvedScore :
      NonProvenancePass unresolvedCandidate context)
    (hNotWorse :
      NonProvenanceNotWorse clearCandidate unresolvedCandidate)
    (hClearStatus :
      candidateStatus clearCandidate = ProvenanceStatus.clear)
    (hUnresolvedStatus :
      candidateStatus unresolvedCandidate =
        ProvenanceStatus.unresolved)
    (hRelevant : context.relevant = true)
    (hMaterial : context.material = true)
    (hNoMitigation : unresolvedCandidate.mitigation = false) :
    frictionRank (policy.decide clearCandidate context) <
      frictionRank (policy.decide unresolvedCandidate context) := by
  have hClearScore : NonProvenancePass clearCandidate context := by
    unfold NonProvenancePass NonProvenanceNotWorse at *
    exact Nat.le_trans hUnresolvedScore hNotWorse
  have hClearDecision :
      policy.decide clearCandidate context =
        AdoptionDisposition.adopt :=
    policy.clearFitPassAdopts clearCandidate context
      hClearContext
      hClearFit hClearScore hClearStatus
  have hUnresolvedNotAdopt :
      Not (policy.decide unresolvedCandidate context =
        AdoptionDisposition.adopt) :=
    policy.unresolvedMaterialUseNotAdopt
      unresolvedCandidate context hUnresolvedFit
      hUnresolvedScore hRelevant hMaterial hNoMitigation
      hUnresolvedStatus
  rw [hClearDecision]
  exact friction_positive_of_not_adopt
    (policy.decide unresolvedCandidate context)
    hUnresolvedNotAdopt

theorem concrete_verified_provenance_adoption_friction_dominance
    (clearCandidate unresolvedCandidate : Candidate)
    (context : AdoptionContext)
    (hClearContext :
      ContextMatchesCandidate clearCandidate context)
    (hUnresolvedContext :
      ContextMatchesCandidate unresolvedCandidate context)
    (hClearFit : clearCandidate.functionalFit = true)
    (hUnresolvedFit : unresolvedCandidate.functionalFit = true)
    (hUnresolvedScore :
      NonProvenancePass unresolvedCandidate context)
    (hNotWorse :
      NonProvenanceNotWorse clearCandidate unresolvedCandidate)
    (hClearStatus :
      candidateStatus clearCandidate = ProvenanceStatus.clear)
    (hUnresolvedStatus :
      candidateStatus unresolvedCandidate =
        ProvenanceStatus.unresolved)
    (hRelevant : context.relevant = true)
    (hMaterial : context.material = true)
    (hNoMitigation : unresolvedCandidate.mitigation = false) :
    frictionRank
        (responsiblePolicy.decide clearCandidate context) <
      frictionRank
        (responsiblePolicy.decide unresolvedCandidate context) :=
  verified_provenance_adoption_friction_dominance
    responsiblePolicy clearCandidate unresolvedCandidate context
    hClearContext hUnresolvedContext
    hClearFit hUnresolvedFit hUnresolvedScore hNotWorse
    hClearStatus hUnresolvedStatus hRelevant hMaterial
    hNoMitigation

/-! ## 6. Hard-gate selection kernel -/

abbrev CandidateSet (alpha : Type u) : Type u := alpha -> Prop
abbrev Selection (alpha : Type u) : Type u := alpha -> Prop

def WithinCandidates
    {alpha : Type u}
    (select : CandidateSet alpha -> Selection alpha) : Prop :=
  forall {set : CandidateSet alpha} {candidate : alpha},
    select set candidate -> set candidate

def SelectionSound
    {alpha : Type u}
    (admissible : alpha -> Prop)
    (select : CandidateSet alpha -> Selection alpha) : Prop :=
  forall {set : CandidateSet alpha} {candidate : alpha},
    select set candidate -> admissible candidate

def NonBlockingComplete
    {alpha : Type u}
    (admissible : alpha -> Prop)
    (select : CandidateSet alpha -> Selection alpha) : Prop :=
  forall {set : CandidateSet alpha},
    (exists candidate, set candidate /\ admissible candidate) ->
      exists selected, select set selected

def UniqueAdmissibleIn
    {alpha : Type u}
    (admissible : alpha -> Prop)
    (set : CandidateSet alpha)
    (candidate : alpha) : Prop :=
  set candidate /\
  admissible candidate /\
  forall other, set other -> admissible other -> other = candidate

def hardGateSelection
    {alpha : Type u}
    (admissible : alpha -> Prop)
    (set : CandidateSet alpha) : Selection alpha :=
  fun candidate => set candidate /\ admissible candidate

theorem hardGate_within
    {alpha : Type u}
    (admissible : alpha -> Prop) :
    WithinCandidates (hardGateSelection admissible) := by
  intro set candidate selected
  exact selected.left

theorem hardGate_sound
    {alpha : Type u}
    (admissible : alpha -> Prop) :
    SelectionSound admissible (hardGateSelection admissible) := by
  intro set candidate selected
  exact selected.right

theorem hardGate_nonblocking
    {alpha : Type u}
    (admissible : alpha -> Prop) :
    NonBlockingComplete admissible
      (hardGateSelection admissible) := by
  intro set existsAdmissible
  obtain ⟨candidate, hInSet, hAdmissible⟩ :=
    existsAdmissible
  exact Exists.intro candidate
    (And.intro hInSet hAdmissible)

theorem unique_clear_candidate_selected_under_hard_gate
    {alpha : Type u}
    {admissible : alpha -> Prop}
    {select : CandidateSet alpha -> Selection alpha}
    {set : CandidateSet alpha}
    {candidate : alpha}
    (within : WithinCandidates select)
    (sound : SelectionSound admissible select)
    (complete : NonBlockingComplete admissible select)
    (unique : UniqueAdmissibleIn admissible set candidate) :
    select set candidate := by
  have existsAdmissible :
      exists x, set x /\ admissible x :=
    Exists.intro candidate
      (And.intro unique.left unique.right.left)
  obtain ⟨selected, hSelected⟩ := complete existsAdmissible
  have hSelectedInSet : set selected := within hSelected
  have hSelectedAdmissible : admissible selected := sound hSelected
  have hSelectedEq :
      selected = candidate :=
    unique.right.right selected hSelectedInSet
      hSelectedAdmissible
  cases hSelectedEq
  exact hSelected

/-! ## 7. Finite verifier-backed case study -/

def originTarget : ProvenanceTarget :=
  {
    artifactId := "artifact:OriginVerified",
    claimId := "claim:evaluation-os:provenance-sensitive",
    specificationId := "spec:evaluation-os",
    specificationVersion := "v1",
    artifactDigest := "digest:origin",
    subjectAgentId := "agent:OriginDeveloper",
    primaryPublishedAt := 20,
    expectedOriginArtifactDigest := "digest:origin",
    authorizingAgentId := "agent:OriginDeveloper",
    authorizationId := "authorization:origin-license",
    expectedDevelopmentRecordDigest :=
      "digest:origin-development-record",
    developmentRecordId := "development:origin"
  }

def laterTarget : ProvenanceTarget :=
  {
    artifactId := "artifact:LaterUnresolved",
    claimId := "claim:evaluation-os:provenance-sensitive",
    specificationId := "spec:evaluation-os",
    specificationVersion := "v1",
    artifactDigest := "digest:later",
    subjectAgentId := "agent:LaterDeveloper",
    primaryPublishedAt := 30,
    expectedOriginArtifactDigest := "digest:origin",
    authorizingAgentId := "agent:OriginDeveloper",
    authorizationId := "authorization:later-from-origin",
    expectedDevelopmentRecordDigest :=
      "digest:later-development-record",
    developmentRecordId := "development:later"
  }

def originDeclaredPrimary : DeclaredPrimaryOrigin :=
  {
    claimId := originTarget.claimId,
    specificationId := originTarget.specificationId,
    specificationVersion := originTarget.specificationVersion,
    artifactDigest := originTarget.artifactDigest,
    subjectAgentId := originTarget.subjectAgentId,
    publishedAt := originTarget.primaryPublishedAt
  }

def originPrimaryRecord : PrimaryEvidenceRecord :=
  {
    claimId := originTarget.claimId,
    specificationId := originTarget.specificationId,
    specificationVersion := originTarget.specificationVersion,
    artifactDigest := originTarget.artifactDigest,
    subjectAgentId := originTarget.subjectAgentId,
    publishedAt := originTarget.primaryPublishedAt
  }

theorem origin_primary_statement :
    (primaryEvidenceQuery originDeclaredPrimary
      originPrimaryRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    originDeclaredPrimary, originPrimaryRecord, originTarget]

def certificateMetaFor
    (certificateId : CertificateId)
    (kind : ProvenanceCertificateKind)
    (query : ProvenanceQuery) : ProvenanceCertificateMeta :=
  {
    certificateId := certificateId,
    claimId := query.claimId,
    specificationId := query.specificationId,
    specificationVersion := query.specificationVersion,
    artifactDigest := query.artifactDigest,
    subjectAgentId := query.subjectAgentId,
    issuerId := query.issuerId,
    issuedAt := 100,
    certificateKind := kind
  }

def certificateForQuery
    (certificateId : CertificateId)
    (kind : ProvenanceCertificateKind)
    (query : ProvenanceQuery)
    (proof : query.statement) :
    CertifiedProvenanceClaim :=
  {
    metadata := certificateMetaFor certificateId kind query,
    statement := query.statement,
    proof := proof
  }

def certificateForQueryWithIssuer
    (certificateId : CertificateId)
    (kind : ProvenanceCertificateKind)
    (query : ProvenanceQuery)
    (issuerId : IssuerId)
    (proof : query.statement) :
    CertifiedProvenanceClaim :=
  {
    metadata := {
      certificateMetaFor certificateId kind query with
      issuerId := issuerId
    },
    statement := query.statement,
    proof := proof
  }

def originPrimaryCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:origin-primary"
    ProvenanceCertificateKind.primary
    (primaryEvidenceQuery originDeclaredPrimary originPrimaryRecord)
    origin_primary_statement

def originVerifiedPrimary :
    VerifiedPrimaryEvidence originTarget :=
  {
    declared := originDeclaredPrimary,
    record := originPrimaryRecord,
    certificate := {
      certificate := originPrimaryCertificate,
      metadataAccepted := by rfl,
      sameStatement := rfl
    },
    targetAccepted := by
      simp [PrimaryEvidenceTargets, originTarget,
        originDeclaredPrimary, originPrimaryRecord]
  }

def originPrimaryVerifierResult :
    Option (VerifiedPrimaryEvidence originTarget) :=
    verifyPrimaryEvidence? originTarget originDeclaredPrimary
      originPrimaryRecord originPrimaryCertificate rfl

theorem origin_primary_verifier_accepts :
    originPrimaryVerifierResult =
      some originVerifiedPrimary := by
  rfl

def originBundle :
    VerifiedProvenanceEvidenceBundle originTarget :=
  {
    primary := originPrimaryVerifierResult,
    authorization := none,
    independentDevelopment := none,
    conflict := none
  }

def laterUnresolvedBundle :
    VerifiedProvenanceEvidenceBundle laterTarget :=
  emptyEvidenceBundle laterTarget

def laterAuthorizationRecord : AuthorizationEvidenceRecord :=
  {
    claimId := laterTarget.claimId,
    specificationId := laterTarget.specificationId,
    specificationVersion := laterTarget.specificationVersion,
    derivativeArtifactDigest := laterTarget.artifactDigest,
    derivativeSubjectAgentId := laterTarget.subjectAgentId,
    originArtifactDigest := laterTarget.expectedOriginArtifactDigest,
    authorizingAgentId := laterTarget.authorizingAgentId,
    authorizationId := laterTarget.authorizationId
  }

theorem later_authorization_statement :
    (authorizationEvidenceQuery laterAuthorizationRecord).statement := by
  simp [authorizationEvidenceQuery,
    AuthorizationRecordInternallyValid,
    laterAuthorizationRecord, laterTarget]

def laterAuthorizationCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:later-authorization"
    ProvenanceCertificateKind.authorization
    (authorizationEvidenceQuery laterAuthorizationRecord)
    later_authorization_statement

def laterVerifiedAuthorization :
    VerifiedAuthorizationEvidence laterTarget :=
  {
    record := laterAuthorizationRecord,
    certificate := {
        certificate := laterAuthorizationCertificate,
        metadataAccepted := by rfl,
        sameStatement := rfl
    },
    targetAccepted := by
      simp [AuthorizationEvidenceTargets,
        laterAuthorizationRecord, laterTarget]
  }

def laterAuthorizationVerifierResult :
    Option (VerifiedAuthorizationEvidence laterTarget) :=
    verifyAuthorizationEvidence? laterTarget
      laterAuthorizationRecord laterAuthorizationCertificate rfl

theorem later_authorization_verifier_accepts :
    laterAuthorizationVerifierResult =
      some laterVerifiedAuthorization := by
  rfl

def laterResolution :
    VerifiedResolutionEvidence laterTarget :=
  VerifiedResolutionEvidence.authorization laterVerifiedAuthorization

def laterResolvedBundle :
    VerifiedProvenanceEvidenceBundle laterTarget :=
  { laterUnresolvedBundle with
    authorization := laterAuthorizationVerifierResult }

theorem later_resolved_bundle_matches_resolution :
    laterResolvedBundle =
      addVerifiedResolution laterUnresolvedBundle laterResolution := by
  rfl

def originAssessment : ProvenanceAssessment :=
  { target := originTarget, evidence := originBundle }

def laterUnresolvedAssessment : ProvenanceAssessment :=
  { target := laterTarget, evidence := laterUnresolvedBundle }

def laterResolvedAssessment : ProvenanceAssessment :=
  { target := laterTarget, evidence := laterResolvedBundle }

def originSignals : MarketSignals :=
  { authority := 5, popularity := 3, adoptionCount := 1 }

def laterSignals : MarketSignals :=
  { authority := 70, popularity := 100, adoptionCount := 25 }

def laterMorePopularSignals : MarketSignals :=
  { authority := 70, popularity := 10000, adoptionCount := 3000 }

def originVerifiedCandidate : Candidate :=
  {
    provenance := originAssessment,
    signals := originSignals,
    functionalFit := true,
    nonProvenanceMerit := 90,
    mitigation := false
  }

def laterUnresolvedCandidate : Candidate :=
  {
    provenance := laterUnresolvedAssessment,
    signals := laterSignals,
    functionalFit := true,
    nonProvenanceMerit := 90,
    mitigation := false
  }

def laterAfterResolutionCandidate : Candidate :=
  addResolutionToCandidate laterUnresolvedCandidate laterResolution

def adopterId : AgentId :=
  "agent:Adopter"

def provenanceSensitiveClaim : ClaimId :=
  "claim:evaluation-os:provenance-sensitive"

def highResponsibilityUse : UseContextId :=
  "use:high-responsibility-adoption"

def unrelatedUse : UseContextId :=
  "use:unrelated-documentation"

def highAssuranceContext : AdoptionContext :=
  {
    adopter := adopterId,
    useContext := highResponsibilityUse,
    claim := provenanceSensitiveClaim,
    relevant := true,
    material := true,
    highResponsibility := true,
    minNonProvenanceMerit := 80
  }

def unrelatedContext : AdoptionContext :=
  {
    adopter := adopterId,
    useContext := unrelatedUse,
    claim := provenanceSensitiveClaim,
    relevant := false,
    material := false,
    highResponsibility := false,
    minNonProvenanceMerit := 80
  }

def laterUnresolvedRecord : ProvenanceRecord :=
  {
    provenance := laterUnresolvedAssessment,
    signals := laterSignals
  }

theorem candidate_scope_uses_target_artifact_and_claim
    (candidate : Candidate)
    (context : AdoptionContext) :
    (candidateScope candidate context).artifact =
        candidate.provenance.target.artifactId /\
      (candidateScope candidate context).claim =
        candidate.provenance.target.claimId := by
  constructor <;> rfl

def mismatchedClaimContext : AdoptionContext :=
  {
    highAssuranceContext with
    claim := "claim:unrelated"
  }

theorem mismatched_claim_context_not_matches :
    Not
      (ContextMatchesCandidate originVerifiedCandidate
        mismatchedClaimContext) := by
  simp [ContextMatchesCandidate, originVerifiedCandidate,
    originAssessment, originTarget, mismatchedClaimContext,
    highAssuranceContext]

theorem context_claim_mismatch_is_rejected :
    responsiblePolicy.decide originVerifiedCandidate
        mismatchedClaimContext =
      AdoptionDisposition.reject := by
  exact responsibleDecision_context_mismatch_rejects
    originVerifiedCandidate mismatchedClaimContext
    mismatched_claim_context_not_matches

theorem context_claim_mismatch_has_no_scoped_finding :
    scopedFinding? originVerifiedCandidate
        mismatchedClaimContext =
      none := by
  exact scopedFinding_context_mismatch_none
    originVerifiedCandidate mismatchedClaimContext
    mismatched_claim_context_not_matches

theorem origin_verified_is_clear :
    candidateStatus originVerifiedCandidate =
      ProvenanceStatus.clear :=
  valid_primary_is_clear originBundle
    (Exists.intro originVerifiedPrimary rfl) rfl

theorem later_unresolved_is_unresolved :
    candidateStatus laterUnresolvedCandidate =
      ProvenanceStatus.unresolved :=
  no_verified_evidence_is_unresolved laterUnresolvedBundle
    (by
      intro hClearance
      cases hClearance with
      | inl hPrimary =>
          obtain ⟨evidence, hEvidence⟩ := hPrimary
          cases hEvidence
      | inr hRest =>
          cases hRest with
          | inl hAuthorization =>
              obtain ⟨evidence, hEvidence⟩ := hAuthorization
              cases hEvidence
          | inr hIndependent =>
              obtain ⟨evidence, hEvidence⟩ := hIndependent
              cases hEvidence)
    (by
      intro hConflict
      obtain ⟨evidence, hEvidence⟩ := hConflict
      cases hEvidence)

theorem later_unresolved_remains_unresolved_after_popularity_increase :
    recordStatus (withPopularity laterUnresolvedRecord 10000) =
      ProvenanceStatus.unresolved :=
  popularity_cannot_clear_unresolved_provenance
    laterUnresolvedRecord 10000 later_unresolved_is_unresolved

theorem later_unresolved_status_has_no_evidence :
    Not
        (HasVerifiedClearanceEvidence laterUnresolvedBundle) /\
      Not
        (HasVerifiedConflictEvidence laterUnresolvedBundle) :=
  unresolved_status_has_no_verified_clearance_or_conflict
    laterUnresolvedBundle later_unresolved_is_unresolved

theorem origin_verified_is_adopted :
    responsiblePolicy.decide originVerifiedCandidate
        highAssuranceContext =
      AdoptionDisposition.adopt :=
  responsibleDecision_clear_fit_pass_adopts
    originVerifiedCandidate highAssuranceContext
    (by rfl)
    (by rfl)
    (by decide)
    origin_verified_is_clear

theorem later_unresolved_requires_review_or_hold :
    RequiresReviewOrHold
      (responsiblePolicy.decide
        laterUnresolvedCandidate highAssuranceContext) :=
  unresolved_material_use_requires_scoped_review
    laterUnresolvedCandidate highAssuranceContext
    (by rfl)
    (by rfl)
    (by decide)
    (by rfl)
    (by rfl)
    (by rfl)
    later_unresolved_is_unresolved

theorem origin_has_strictly_lower_adoption_friction :
    frictionRank
        (responsiblePolicy.decide
          originVerifiedCandidate highAssuranceContext) <
      frictionRank
        (responsiblePolicy.decide
          laterUnresolvedCandidate highAssuranceContext) :=
  verified_provenance_adoption_friction_dominance
    responsiblePolicy
    originVerifiedCandidate
    laterUnresolvedCandidate
    highAssuranceContext
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by decide)
    (by decide)
    origin_verified_is_clear
    later_unresolved_is_unresolved
    (by rfl)
    (by rfl)
    (by rfl)

theorem later_after_resolution_is_clear :
    candidateStatus laterAfterResolutionCandidate =
      ProvenanceStatus.clear :=
  add_verified_resolution_is_clear
    laterUnresolvedBundle laterResolution
    later_unresolved_is_unresolved

theorem later_after_resolution_is_adopted :
    responsiblePolicy.decide
        laterAfterResolutionCandidate highAssuranceContext =
      AdoptionDisposition.adopt :=
  (valid_resolution_clears_scoped_review
    laterUnresolvedCandidate highAssuranceContext
    laterResolution later_unresolved_is_unresolved
    (by rfl)
    (by rfl) (by decide)).left

theorem later_after_resolution_review_is_removed :
    scopedFinding? laterAfterResolutionCandidate
        highAssuranceContext =
      none :=
  (valid_resolution_clears_scoped_review
    laterUnresolvedCandidate highAssuranceContext
    laterResolution later_unresolved_is_unresolved
    (by rfl)
    (by rfl) (by decide)).right

/-! ## 8. Counterexamples and tampering checks -/

def scoreByPopularity
    {target : ProvenanceTarget}
    (baseUtility : Nat)
    (signals : MarketSignals)
    (provenancePenalty : Nat)
    (bundle : VerifiedProvenanceEvidenceBundle target) : Nat :=
  baseUtility + signals.popularity -
    match provenanceStatus bundle with
    | ProvenanceStatus.clear => 0
    | ProvenanceStatus.unresolved => provenancePenalty
    | ProvenanceStatus.conflicted => provenancePenalty + 20

theorem popularity_bonus_can_mask_unresolved_provenance :
    scoreByPopularity 80 laterMorePopularSignals 10
        laterUnresolvedBundle >
      scoreByPopularity 80 originSignals 10 originBundle /\
    provenanceStatus laterUnresolvedBundle =
      ProvenanceStatus.unresolved /\
    provenanceStatus originBundle = ProvenanceStatus.clear := by
  decide

inductive PublicationChoice where
  | earliestMismatched
  | laterMatching
deriving DecidableEq

def requiredPrimaryOrigin : DeclaredPrimaryOrigin :=
  {
    claimId := originTarget.claimId,
    specificationId := originTarget.specificationId,
    specificationVersion := originTarget.specificationVersion,
    artifactDigest := originTarget.artifactDigest,
    subjectAgentId := originTarget.subjectAgentId,
    publishedAt := originTarget.primaryPublishedAt
  }

def publicationRecord : PublicationChoice -> PrimaryEvidenceRecord
  | PublicationChoice.earliestMismatched =>
      {
        claimId := originTarget.claimId,
        specificationId := originTarget.specificationId,
        specificationVersion := originTarget.specificationVersion,
        artifactDigest := "digest:mismatched-earliest",
        subjectAgentId := originTarget.subjectAgentId,
        publishedAt := 10
      }
  | PublicationChoice.laterMatching =>
      originPrimaryRecord

def earliestTimestampOnlyChoice : PublicationChoice :=
  PublicationChoice.earliestMismatched

def earliestMismatchedDeclared : DeclaredPrimaryOrigin :=
  {
    claimId := originTarget.claimId,
    specificationId := originTarget.specificationId,
    specificationVersion := originTarget.specificationVersion,
    artifactDigest := "digest:mismatched-earliest",
    subjectAgentId := originTarget.subjectAgentId,
    publishedAt := 10
  }

theorem earliest_mismatched_statement :
    (primaryEvidenceQuery earliestMismatchedDeclared
      (publicationRecord
        PublicationChoice.earliestMismatched)).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    earliestMismatchedDeclared, publicationRecord,
    originTarget]

def earliestMismatchedCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:earliest-mismatched"
    ProvenanceCertificateKind.primary
    (primaryEvidenceQuery earliestMismatchedDeclared
      (publicationRecord
        PublicationChoice.earliestMismatched))
    earliest_mismatched_statement

theorem earliest_timestamp_alone_is_not_clearance :
    earliestTimestampOnlyChoice =
        PublicationChoice.earliestMismatched /\
    Not
      (PrimaryEvidenceTargets originTarget
        earliestMismatchedDeclared
        (publicationRecord earliestTimestampOnlyChoice)) /\
    PrimaryEvidenceTargets originTarget
      originDeclaredPrimary
      (publicationRecord PublicationChoice.laterMatching) /\
    verifyPrimaryEvidence? originTarget
        earliestMismatchedDeclared
        (publicationRecord earliestTimestampOnlyChoice)
        earliestMismatchedCertificate rfl = none := by
  constructor
  · rfl
  constructor
  · simp [PrimaryEvidenceTargets, earliestMismatchedDeclared,
      publicationRecord, originTarget]
  constructor
  · simp [PrimaryEvidenceTargets, originDeclaredPrimary,
      originPrimaryRecord, publicationRecord, originTarget]
  · rfl

def RespectsScopeLimitation
    (propagate : ScopedFinding -> AdoptionScope -> Prop) : Prop :=
  forall finding target,
    Not (RelatedScope finding.scope target) ->
      Not (propagate finding target)

def globalContagionPolicy
    (finding : ScopedFinding)
    (_target : AdoptionScope) : Prop :=
  FindingRequiresReviewOrHold finding

def laterReviewFinding : ScopedFinding :=
  {
    scope := candidateScope laterUnresolvedCandidate
      highAssuranceContext,
    status := ProvenanceStatus.unresolved,
    disposition := AdoptionDisposition.hold
  }

def unrelatedScope : AdoptionScope :=
  candidateScope laterUnresolvedCandidate unrelatedContext

theorem unrelated_use_context_is_unaffected :
    Not (ReviewPropagatesTo laterReviewFinding unrelatedScope) := by
  apply scoped_review_does_not_propagate_to_unrelated_scope
  decide

theorem global_contagion_policy_violates_scope_limitation :
    Not (RespectsScopeLimitation globalContagionPolicy) := by
  intro respects
  have hUnrelated :
      Not (RelatedScope laterReviewFinding.scope
        unrelatedScope) := by
    decide
  have hPropagates :
      globalContagionPolicy laterReviewFinding
        unrelatedScope := by
    unfold globalContagionPolicy FindingRequiresReviewOrHold
      RequiresReviewOrHold
    exact Or.inr rfl
  exact respects laterReviewFinding unrelatedScope
    hUnrelated hPropagates

def tamperedPrimaryDeclared
    (claimId : ClaimId)
    (specificationId : SpecificationId)
    (specificationVersion : SpecificationVersion)
    (artifactDigest : ArtifactDigest)
    (subjectAgentId : AgentId)
    (publishedAt : Timestamp) : DeclaredPrimaryOrigin :=
  {
    claimId := claimId,
    specificationId := specificationId,
    specificationVersion := specificationVersion,
    artifactDigest := artifactDigest,
    subjectAgentId := subjectAgentId,
    publishedAt := publishedAt
  }

def tamperedPrimaryRecord
    (claimId : ClaimId)
    (specificationId : SpecificationId)
    (specificationVersion : SpecificationVersion)
    (artifactDigest : ArtifactDigest)
    (subjectAgentId : AgentId)
    (publishedAt : Timestamp) : PrimaryEvidenceRecord :=
  {
    claimId := claimId,
    specificationId := specificationId,
    specificationVersion := specificationVersion,
    artifactDigest := artifactDigest,
    subjectAgentId := subjectAgentId,
    publishedAt := publishedAt
  }

def tamperedPrimaryCertificate
    (certificateId : CertificateId)
    (kind : ProvenanceCertificateKind)
    (declared : DeclaredPrimaryOrigin)
    (record : PrimaryEvidenceRecord)
    (proof :
      (primaryEvidenceQuery declared record).statement) :
    CertifiedProvenanceClaim :=
  certificateForQuery certificateId kind
    (primaryEvidenceQuery declared record) proof

def wrongDigestDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    "digest:wrong" originTarget.subjectAgentId
    originTarget.primaryPublishedAt

def wrongDigestRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    "digest:wrong" originTarget.subjectAgentId
    originTarget.primaryPublishedAt

theorem wrong_digest_primary_statement :
    (primaryEvidenceQuery wrongDigestDeclared
      wrongDigestRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongDigestDeclared, wrongDigestRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongDigestPrimaryCertificate : CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-digest"
    ProvenanceCertificateKind.primary wrongDigestDeclared
    wrongDigestRecord wrong_digest_primary_statement

theorem tampered_primary_digest_is_rejected :
    verifyPrimaryEvidence? originTarget wrongDigestDeclared
        wrongDigestRecord wrongDigestPrimaryCertificate rfl = none := by
  rfl

def wrongKindPrimaryCertificate : CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-kind"
    ProvenanceCertificateKind.authorization
    originDeclaredPrimary originPrimaryRecord
    origin_primary_statement

theorem tampered_primary_kind_is_rejected :
    verifyPrimaryEvidence? originTarget originDeclaredPrimary
        originPrimaryRecord wrongKindPrimaryCertificate rfl = none := by
  rfl

def wrongClaimDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared "claim:wrong"
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest originTarget.subjectAgentId
    originTarget.primaryPublishedAt

def wrongClaimRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord "claim:wrong"
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest originTarget.subjectAgentId
    originTarget.primaryPublishedAt

theorem wrong_claim_primary_statement :
    (primaryEvidenceQuery wrongClaimDeclared
      wrongClaimRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongClaimDeclared, wrongClaimRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongClaimPrimaryCertificate : CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-claim"
    ProvenanceCertificateKind.primary wrongClaimDeclared
    wrongClaimRecord wrong_claim_primary_statement

theorem tampered_primary_claim_is_rejected :
    verifyPrimaryEvidence? originTarget wrongClaimDeclared
        wrongClaimRecord wrongClaimPrimaryCertificate rfl = none := by
  rfl

def wrongSpecificationDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared originTarget.claimId "spec:wrong"
    originTarget.specificationVersion originTarget.artifactDigest
    originTarget.subjectAgentId originTarget.primaryPublishedAt

def wrongSpecificationRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord originTarget.claimId "spec:wrong"
    originTarget.specificationVersion originTarget.artifactDigest
    originTarget.subjectAgentId originTarget.primaryPublishedAt

theorem wrong_specification_primary_statement :
    (primaryEvidenceQuery wrongSpecificationDeclared
      wrongSpecificationRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongSpecificationDeclared, wrongSpecificationRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongSpecificationPrimaryCertificate :
    CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-specification"
    ProvenanceCertificateKind.primary wrongSpecificationDeclared
    wrongSpecificationRecord
    wrong_specification_primary_statement

theorem tampered_primary_specification_is_rejected :
    verifyPrimaryEvidence? originTarget wrongSpecificationDeclared
        wrongSpecificationRecord wrongSpecificationPrimaryCertificate
        rfl = none := by
  rfl

def wrongVersionDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared originTarget.claimId
    originTarget.specificationId "v-wrong"
    originTarget.artifactDigest originTarget.subjectAgentId
    originTarget.primaryPublishedAt

def wrongVersionRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord originTarget.claimId
    originTarget.specificationId "v-wrong"
    originTarget.artifactDigest originTarget.subjectAgentId
    originTarget.primaryPublishedAt

theorem wrong_version_primary_statement :
    (primaryEvidenceQuery wrongVersionDeclared
      wrongVersionRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongVersionDeclared, wrongVersionRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongVersionPrimaryCertificate : CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-version"
    ProvenanceCertificateKind.primary wrongVersionDeclared
    wrongVersionRecord wrong_version_primary_statement

theorem tampered_primary_version_is_rejected :
    verifyPrimaryEvidence? originTarget wrongVersionDeclared
        wrongVersionRecord wrongVersionPrimaryCertificate rfl =
      none := by
  rfl

def wrongSubjectDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest "agent:wrong-subject"
    originTarget.primaryPublishedAt

def wrongSubjectRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest "agent:wrong-subject"
    originTarget.primaryPublishedAt

theorem wrong_subject_primary_statement :
    (primaryEvidenceQuery wrongSubjectDeclared
      wrongSubjectRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongSubjectDeclared, wrongSubjectRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongSubjectPrimaryCertificate : CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-subject"
    ProvenanceCertificateKind.primary wrongSubjectDeclared
    wrongSubjectRecord wrong_subject_primary_statement

theorem tampered_primary_subject_is_rejected :
    verifyPrimaryEvidence? originTarget wrongSubjectDeclared
        wrongSubjectRecord wrongSubjectPrimaryCertificate rfl =
      none := by
  rfl

def wrongPublishedAtDeclared : DeclaredPrimaryOrigin :=
  tamperedPrimaryDeclared originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest originTarget.subjectAgentId 10

def wrongPublishedAtRecord : PrimaryEvidenceRecord :=
  tamperedPrimaryRecord originTarget.claimId
    originTarget.specificationId originTarget.specificationVersion
    originTarget.artifactDigest originTarget.subjectAgentId 10

theorem wrong_published_at_primary_statement :
    (primaryEvidenceQuery wrongPublishedAtDeclared
      wrongPublishedAtRecord).statement := by
  simp [primaryEvidenceQuery, PrimaryWithinDeclaredUniverse,
    wrongPublishedAtDeclared, wrongPublishedAtRecord,
    tamperedPrimaryDeclared, tamperedPrimaryRecord, originTarget]

def wrongPublishedAtPrimaryCertificate :
    CertifiedProvenanceClaim :=
  tamperedPrimaryCertificate "cert:wrong-published-at"
    ProvenanceCertificateKind.primary wrongPublishedAtDeclared
    wrongPublishedAtRecord wrong_published_at_primary_statement

theorem tampered_primary_published_at_is_rejected :
    verifyPrimaryEvidence? originTarget wrongPublishedAtDeclared
        wrongPublishedAtRecord wrongPublishedAtPrimaryCertificate
        rfl = none := by
  rfl

def wrongAuthorizationSubject : AuthorizationEvidenceRecord :=
  {
    laterAuthorizationRecord with
    derivativeSubjectAgentId := "agent:wrong-subject"
  }

theorem wrong_authorization_subject_statement :
    (authorizationEvidenceQuery wrongAuthorizationSubject).statement := by
  simp [authorizationEvidenceQuery,
    AuthorizationRecordInternallyValid,
    wrongAuthorizationSubject, laterAuthorizationRecord,
    laterTarget]

def wrongAuthorizationSubjectCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-authorization-subject"
    ProvenanceCertificateKind.authorization
    (authorizationEvidenceQuery wrongAuthorizationSubject)
    wrong_authorization_subject_statement

theorem tampered_authorization_subject_is_rejected :
    verifyAuthorizationEvidence? laterTarget
        wrongAuthorizationSubject
        wrongAuthorizationSubjectCertificate rfl = none := by
  rfl

def wrongAuthorizationOriginDigest : AuthorizationEvidenceRecord :=
  {
    laterAuthorizationRecord with
    originArtifactDigest := "digest:wrong-origin"
  }

theorem wrong_authorization_origin_digest_statement :
    (authorizationEvidenceQuery
      wrongAuthorizationOriginDigest).statement := by
  simp [authorizationEvidenceQuery,
    AuthorizationRecordInternallyValid,
    wrongAuthorizationOriginDigest, laterAuthorizationRecord,
    laterTarget]

def wrongAuthorizationOriginDigestCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-authorization-origin"
    ProvenanceCertificateKind.authorization
    (authorizationEvidenceQuery wrongAuthorizationOriginDigest)
    wrong_authorization_origin_digest_statement

theorem tampered_authorization_origin_digest_is_rejected :
    verifyAuthorizationEvidence? laterTarget
        wrongAuthorizationOriginDigest
        wrongAuthorizationOriginDigestCertificate rfl = none := by
  rfl

def wrongIssuerAuthorizationCertificate :
    CertifiedProvenanceClaim :=
  certificateForQueryWithIssuer "cert:wrong-authorization-issuer"
    ProvenanceCertificateKind.authorization
    (authorizationEvidenceQuery laterAuthorizationRecord)
    "issuer:wrong"
    later_authorization_statement

theorem tampered_authorization_issuer_is_rejected :
    verifyAuthorizationEvidence? laterTarget
        laterAuthorizationRecord
        wrongIssuerAuthorizationCertificate rfl = none := by
  rfl

def wrongKindAuthorizationCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-authorization-kind"
    ProvenanceCertificateKind.primary
    (authorizationEvidenceQuery laterAuthorizationRecord)
    later_authorization_statement

theorem tampered_authorization_kind_is_rejected :
    verifyAuthorizationEvidence? laterTarget
        laterAuthorizationRecord
        wrongKindAuthorizationCertificate rfl = none := by
  rfl

def wrongAuthorizationAuthorizer : AuthorizationEvidenceRecord :=
  {
    laterAuthorizationRecord with
    authorizingAgentId := "agent:wrong-authorizer"
  }

theorem wrong_authorization_authorizer_statement :
    (authorizationEvidenceQuery
      wrongAuthorizationAuthorizer).statement := by
  simp [authorizationEvidenceQuery,
    AuthorizationRecordInternallyValid,
    wrongAuthorizationAuthorizer, laterAuthorizationRecord,
    laterTarget]

def wrongAuthorizationAuthorizerCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-authorization-authorizer"
    ProvenanceCertificateKind.authorization
    (authorizationEvidenceQuery wrongAuthorizationAuthorizer)
    wrong_authorization_authorizer_statement

theorem tampered_authorization_authorizer_is_rejected :
    verifyAuthorizationEvidence? laterTarget
        wrongAuthorizationAuthorizer
        wrongAuthorizationAuthorizerCertificate rfl = none := by
  rfl

def emptyAuthorizationIdRecord : AuthorizationEvidenceRecord :=
  {
    laterAuthorizationRecord with
    authorizationId := ""
  }

theorem tampered_authorization_empty_id_is_rejected :
    verifyAuthorizationRecordBinding laterTarget
      emptyAuthorizationIdRecord = false := by
  rfl

def laterIndependentRecord :
    IndependentDevelopmentEvidenceRecord :=
  {
    claimId := laterTarget.claimId,
    specificationId := laterTarget.specificationId,
    specificationVersion := laterTarget.specificationVersion,
    artifactDigest := laterTarget.artifactDigest,
    subjectAgentId := laterTarget.subjectAgentId,
    developmentRecordDigest :=
      laterTarget.expectedDevelopmentRecordDigest,
    developmentRecordId := laterTarget.developmentRecordId
  }

theorem later_independent_statement :
    (independentDevelopmentEvidenceQuery
      laterIndependentRecord).statement := by
  simp [independentDevelopmentEvidenceQuery,
    IndependentDevelopmentRecordInternallyValid,
    laterIndependentRecord, laterTarget]

def laterIndependentCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:later-independent"
    ProvenanceCertificateKind.independentDevelopment
    (independentDevelopmentEvidenceQuery laterIndependentRecord)
    later_independent_statement

def laterVerifiedIndependent :
    VerifiedIndependentDevelopmentEvidence laterTarget :=
  {
    record := laterIndependentRecord,
    certificate := {
      certificate := laterIndependentCertificate,
      metadataAccepted := by rfl,
      sameStatement := rfl
    },
    targetAccepted := by
      simp [IndependentDevelopmentEvidenceTargets,
        laterIndependentRecord, laterTarget]
  }

def laterIndependentVerifierResult :
    Option (VerifiedIndependentDevelopmentEvidence laterTarget) :=
  verifyIndependentDevelopmentEvidence? laterTarget
    laterIndependentRecord laterIndependentCertificate rfl

theorem later_independent_verifier_accepts :
    laterIndependentVerifierResult =
      some laterVerifiedIndependent := by
  rfl

def wrongIndependentDigest :
    IndependentDevelopmentEvidenceRecord :=
  {
    laterIndependentRecord with
    developmentRecordDigest := "digest:wrong-development-record"
  }

theorem wrong_independent_digest_statement :
    (independentDevelopmentEvidenceQuery
      wrongIndependentDigest).statement := by
  simp [independentDevelopmentEvidenceQuery,
    IndependentDevelopmentRecordInternallyValid,
    wrongIndependentDigest, laterIndependentRecord,
    laterTarget]

def wrongIndependentDigestCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-independent-digest"
    ProvenanceCertificateKind.independentDevelopment
    (independentDevelopmentEvidenceQuery wrongIndependentDigest)
    wrong_independent_digest_statement

theorem tampered_independent_digest_is_rejected :
    verifyIndependentDevelopmentEvidence? laterTarget
        wrongIndependentDigest
        wrongIndependentDigestCertificate rfl = none := by
  rfl

def wrongIndependentSubject :
    IndependentDevelopmentEvidenceRecord :=
  {
    laterIndependentRecord with
    subjectAgentId := "agent:wrong-independent-subject"
  }

theorem wrong_independent_subject_statement :
    (independentDevelopmentEvidenceQuery
      wrongIndependentSubject).statement := by
  simp [independentDevelopmentEvidenceQuery,
    IndependentDevelopmentRecordInternallyValid,
    wrongIndependentSubject, laterIndependentRecord,
    laterTarget]

def wrongIndependentSubjectCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:wrong-independent-subject"
    ProvenanceCertificateKind.independentDevelopment
    (independentDevelopmentEvidenceQuery wrongIndependentSubject)
    wrong_independent_subject_statement

theorem tampered_independent_subject_is_rejected :
    verifyIndependentDevelopmentEvidence? laterTarget
        wrongIndependentSubject
        wrongIndependentSubjectCertificate rfl = none := by
  rfl

def originConflictAssertionLeft : ProvenanceAssertionRecord :=
  {
    target := originTarget,
    assertionId := "assertion:origin-primary-left",
    issuerId := "issuer:left",
    assertionKind :=
      ProvenanceAssertionKind.exclusivePrimary
        "agent:OriginDeveloper"
  }

def originConflictAssertionRight : ProvenanceAssertionRecord :=
  {
    target := originTarget,
    assertionId := "assertion:origin-primary-right",
    issuerId := "issuer:right",
    assertionKind :=
      ProvenanceAssertionKind.exclusivePrimary
        "agent:AlternativeOrigin"
  }

theorem origin_conflict_left_statement :
    (assertionEvidenceQuery originConflictAssertionLeft).statement := by
  simp [assertionEvidenceQuery, ProvenanceAssertionInternallyValid,
    originConflictAssertionLeft]

theorem origin_conflict_right_statement :
    (assertionEvidenceQuery originConflictAssertionRight).statement := by
  simp [assertionEvidenceQuery, ProvenanceAssertionInternallyValid,
    originConflictAssertionRight]

def originConflictLeftCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:conflict-left"
    ProvenanceCertificateKind.conflict
    (assertionEvidenceQuery originConflictAssertionLeft)
    origin_conflict_left_statement

def originConflictRightCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:conflict-right"
    ProvenanceCertificateKind.conflict
    (assertionEvidenceQuery originConflictAssertionRight)
    origin_conflict_right_statement

def originVerifiedConflict :
    VerifiedConflictEvidence originTarget :=
  {
    left := {
      record := originConflictAssertionLeft,
      certificate := {
        certificate := originConflictLeftCertificate,
        metadataAccepted := by rfl,
        sameStatement := rfl
      },
      targetAccepted := by
        simp [AssertionRecordWithinTarget, originTarget,
          originConflictAssertionLeft]
    },
    right := {
      record := originConflictAssertionRight,
      certificate := {
        certificate := originConflictRightCertificate,
        metadataAccepted := by rfl,
        sameStatement := rfl
      },
      targetAccepted := by
        simp [AssertionRecordWithinTarget, originTarget,
          originConflictAssertionRight]
    },
    exclusive := by
      simp [MutuallyExclusiveAssertions,
        mutuallyExclusiveAssertionsBool,
        originConflictAssertionLeft,
        originConflictAssertionRight, originTarget]
  }

theorem origin_conflict_verifier_accepts :
    verifyConflictEvidence? originTarget
        originConflictAssertionLeft originConflictLeftCertificate rfl
        originConflictAssertionRight originConflictRightCertificate rfl =
      some originVerifiedConflict := by
  rfl

def conflictBundle :
    VerifiedProvenanceEvidenceBundle originTarget :=
  {
    primary := some originVerifiedPrimary,
    authorization := none,
    independentDevelopment := none,
    conflict := some originVerifiedConflict
  }

theorem verified_conflict_example_is_conflicted :
    provenanceStatus conflictBundle =
      ProvenanceStatus.conflicted :=
  verified_conflict_takes_precedence conflictBundle
    (Exists.intro originVerifiedConflict rfl)

def sameOriginAssertionRight : ProvenanceAssertionRecord :=
  {
    target := originTarget,
    assertionId := "assertion:origin-primary-same-origin",
    issuerId := "issuer:same-origin",
    assertionKind :=
      ProvenanceAssertionKind.exclusivePrimary
        "agent:OriginDeveloper"
  }

theorem same_origin_right_statement :
    (assertionEvidenceQuery sameOriginAssertionRight).statement := by
  simp [assertionEvidenceQuery, ProvenanceAssertionInternallyValid,
    sameOriginAssertionRight]

def sameOriginRightCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:same-origin-right"
    ProvenanceCertificateKind.conflict
    (assertionEvidenceQuery sameOriginAssertionRight)
    same_origin_right_statement

theorem same_origin_assertions_do_not_form_conflict :
    verifyConflictEvidence? originTarget
        originConflictAssertionLeft originConflictLeftCertificate rfl
        sameOriginAssertionRight sameOriginRightCertificate rfl =
      none := by
  rfl

def differentTargetConflictAssertion : ProvenanceAssertionRecord :=
  {
    originConflictAssertionRight with
    target := laterTarget
  }

theorem different_target_conflict_statement :
    (assertionEvidenceQuery
      differentTargetConflictAssertion).statement := by
  simp [assertionEvidenceQuery, ProvenanceAssertionInternallyValid,
    differentTargetConflictAssertion, originConflictAssertionRight]

def differentTargetConflictCertificate :
    CertifiedProvenanceClaim :=
  certificateForQuery "cert:conflict-different-target"
    ProvenanceCertificateKind.conflict
    (assertionEvidenceQuery differentTargetConflictAssertion)
    different_target_conflict_statement

theorem conflict_different_target_is_rejected :
    verifyConflictEvidence? originTarget
        originConflictAssertionLeft originConflictLeftCertificate rfl
        differentTargetConflictAssertion
        differentTargetConflictCertificate rfl = none := by
  rfl

def wrongKindConflictCertificate : CertifiedProvenanceClaim :=
  certificateForQuery "cert:conflict-wrong-kind"
    ProvenanceCertificateKind.primary
    (assertionEvidenceQuery originConflictAssertionLeft)
    origin_conflict_left_statement

theorem conflict_wrong_kind_is_rejected :
    verifyConflictEvidence? originTarget
        originConflictAssertionLeft wrongKindConflictCertificate rfl
        originConflictAssertionRight originConflictRightCertificate rfl =
      none := by
  rfl

/-! ## 9. Finite hard-gate example -/

inductive FiniteAdoptionCandidate where
  | OriginVerified
  | LaterUnresolved
deriving DecidableEq

def finiteCandidateToCandidate :
    FiniteAdoptionCandidate -> Candidate
  | FiniteAdoptionCandidate.OriginVerified =>
      originVerifiedCandidate
  | FiniteAdoptionCandidate.LaterUnresolved =>
      laterUnresolvedCandidate

def finitePresentedCandidates :
    CandidateSet FiniteAdoptionCandidate :=
  fun _candidate => True

def finiteClearFitAdmissible
    (candidate : FiniteAdoptionCandidate) : Prop :=
  let concrete := finiteCandidateToCandidate candidate
  concrete.functionalFit = true /\
  NonProvenancePass concrete highAssuranceContext /\
  candidateStatus concrete = ProvenanceStatus.clear

theorem finite_origin_admissible :
    finiteClearFitAdmissible
      FiniteAdoptionCandidate.OriginVerified := by
  unfold finiteClearFitAdmissible finiteCandidateToCandidate
  exact And.intro (by rfl)
    (And.intro (by decide) origin_verified_is_clear)

theorem finite_later_not_admissible :
    Not
      (finiteClearFitAdmissible
        FiniteAdoptionCandidate.LaterUnresolved) := by
  intro h
  have hClear :
      candidateStatus laterUnresolvedCandidate =
        ProvenanceStatus.clear := by
    exact h.right.right
  rw [later_unresolved_is_unresolved] at hClear
  cases hClear

theorem finite_origin_unique_clear :
    UniqueAdmissibleIn finiteClearFitAdmissible
      finitePresentedCandidates
      FiniteAdoptionCandidate.OriginVerified := by
  constructor
  · trivial
  constructor
  · exact finite_origin_admissible
  · intro other _hInSet hAdmissible
    cases other with
    | OriginVerified =>
        rfl
    | LaterUnresolved =>
        exact False.elim
          (finite_later_not_admissible hAdmissible)

theorem origin_verified_selected_under_hard_gate_case :
    hardGateSelection finiteClearFitAdmissible
      finitePresentedCandidates
      FiniteAdoptionCandidate.OriginVerified :=
  unique_clear_candidate_selected_under_hard_gate
    (hardGate_within finiteClearFitAdmissible)
    (hardGate_sound finiteClearFitAdmissible)
    (hardGate_nonblocking finiteClearFitAdmissible)
    finite_origin_unique_clear

/-! ## 10. Kernel audit commands -/

#print axioms verifyCertificateMetadata_sound
#print axioms VerifiedCertificateFor.provesQuery
#print axioms verifyPrimaryEvidence_some_sound
#print axioms verifyAuthorizationEvidence_some_sound
#print axioms verifyIndependentDevelopmentEvidence_some_sound
#print axioms verifyConflictEvidence_some_sound
#print axioms clear_status_has_verified_clearance_evidence
#print axioms conflicted_status_has_verified_conflict_evidence
#print axioms unresolved_status_has_no_verified_clearance_or_conflict
#print axioms no_verified_clearance_cannot_be_clear
#print axioms provenance_status_invariant_under_market_signals
#print axioms popularity_cannot_clear_unresolved_provenance
#print axioms unresolved_material_use_requires_scoped_review
#print axioms valid_resolution_clears_scoped_review
#print axioms scoped_review_does_not_propagate_to_unrelated_scope
#print axioms verified_provenance_adoption_friction_dominance
#print axioms concrete_verified_provenance_adoption_friction_dominance
#print axioms unique_clear_candidate_selected_under_hard_gate
#print axioms popularity_bonus_can_mask_unresolved_provenance
#print axioms earliest_timestamp_alone_is_not_clearance
#print axioms global_contagion_policy_violates_scope_limitation
#print axioms tampered_primary_digest_is_rejected
#print axioms tampered_primary_kind_is_rejected
#print axioms tampered_authorization_subject_is_rejected
#print axioms tampered_authorization_origin_digest_is_rejected
#print axioms tampered_authorization_issuer_is_rejected
#print axioms tampered_authorization_kind_is_rejected
#print axioms tampered_independent_digest_is_rejected
#print axioms tampered_independent_subject_is_rejected
#print axioms conflict_different_target_is_rejected
#print axioms conflict_wrong_kind_is_rejected
#print axioms candidate_scope_uses_target_artifact_and_claim
#print axioms context_claim_mismatch_is_rejected
#print axioms context_claim_mismatch_has_no_scoped_finding
#print axioms same_origin_assertions_do_not_form_conflict

end ProofCarryingProvenance
