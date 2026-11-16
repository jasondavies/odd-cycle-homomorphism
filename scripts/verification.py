"""Validation that remains active under Python's -O and -OO modes."""


class VerificationError(RuntimeError):
    """A construction, certificate, or audit failed validation."""


def require(condition, message="Verification failed"):
    if not condition:
        raise VerificationError(message)
