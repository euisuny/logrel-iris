-Q . logrel
# We sometimes want to locally override notation, and there is no good way to do that with scopes.
-arg -w -arg -notation-overridden
# Cannot use non-canonical projections as it causes massive unification failures
# (https://github.com/coq/coq/issues/6294).
-arg -w -arg -redundant-canonical-projection
lang.v
rules.v
typing.v
logrel.v
soundness.v
fundamental.v
