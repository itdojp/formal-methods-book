# Tamarin replay challenge example

This fictional protocol shares a symmetric key between a client and a server.
The server publishes a fresh challenge, and the client returns an encrypted
`<Client, Server, nonce>` tuple. The Dolev–Yao network attacker mediates every
`Out` and `In` fact.

- `replay-flawed.spthy` stores `OpenChallenge` as a persistent fact. The same
  response can therefore be accepted more than once, and `No_Replay` is
  falsified.
- `replay-fixed.spthy` stores `OpenChallenge` as a linear fact. Acceptance
  consumes it, and all four stated lemmas are verified under this symbolic
  model and proof configuration.

The example does not prove cryptographic implementation correctness,
side-channel resistance, random-number quality, key-compromise behavior, or
computational soundness. `Response_Authentication` is non-injective
correspondence; the separate `No_Replay` lemma expresses one-to-one acceptance.
Attack graphs preserve model constants, so every model is public teaching input
and must never contain real keys, credentials, tenant identifiers, or private
deployment names.
Use the manifest runner so the pinned Tamarin/Maude versions, limits, expected
results, and retained artifacts are checked together.

```bash
node scripts/run-example-manifest.js --id tamarin-replay-flawed
node scripts/run-example-manifest.js --id tamarin-replay-fixed
```
