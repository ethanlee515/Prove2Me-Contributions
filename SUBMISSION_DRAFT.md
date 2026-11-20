# Prove2Me disproof submission for review

No authenticated or submission request has been sent to Prove2Me. The API key
file has not been read or copied.

| Field | Prepared value |
| --- | --- |
| Endpoint | `POST https://prove2.me/api/v1/verify` |
| `theorem_id` | `4cc55ca0-e623-46d7-895b-1626a0b94d38` |
| `proof_type` | `disprove` |
| `file` | `Solutions/Sol_MatchIndiff_PublicSM_lemma_D_17.lean` |
| `explanation` | Entire contents of `submission_explanation.md` |

Prepared-file SHA-256 hashes for review:

- Lean file: `F38A1027EE17D4BB10D6973F07F9CEF44DB7C10D351E6F4A9A279D0834561DDA`
- Explanation: `335DD13383CD34E6B1FC2A5424C13CC350A1B31332745C1409F63622FC9D18FC`

Before the POST, the API key is exchanged at `POST /api/v1/agent/refresh` for
an access token; the key is not the bearer token used on `/verify`. The theorem
is public, so a successful disproof and its explanation will be public. The
account tied to the key receives the platform's submission attribution. The
explanation includes the collaborators' names and affiliations as a visible
joint-discovery note; the documented `/verify` fields have no separate
coauthor or contributor field.

The proof file contains a top-level `theorem solution`, negates the full target
type, imports the two published definitions, and does not import the target
theorem. It compiles locally with Lean 4.33.1 and mathlib `0df444a`. The
`StatementMatch.lean` check confirms the solution's type matches the published
declaration. The prose credit can be edited later through `PATCH
/api/v1/submissions/:id`; the Lean file cannot be edited after submission.
