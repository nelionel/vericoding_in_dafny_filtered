"""Backend-aware provider helpers for the clean evaluator."""

from __future__ import annotations

from typing import Callable, Tuple

from vericoding.core.llm_providers import (
    LLMProvider,
    create_llm_provider,
)

from clean_eval.vllm_provider import VLLMProvider


ProviderFactory = Callable[[], Tuple[LLMProvider, str]]


def create_provider_for_backend(
    backend: str,
    llm_name: str,
    vllm_base_url: str,
    vllm_api_key: str,
) -> tuple[str, ProviderFactory]:
    """
    Return a tuple of (resolved_model_name, provider_factory) for the requested backend.
    """

    backend = backend.lower()
    if backend == "openrouter":
        # Call once to resolve actual provider/model, then create a lightweight factory.
        _, resolved = create_llm_provider(llm_name)

        def factory() -> tuple[LLMProvider, str]:
            return create_llm_provider(llm_name)

        return resolved, factory

    if backend == "vllm":
        def factory() -> tuple[LLMProvider, str]:
            provider = VLLMProvider(
                base_url=vllm_base_url,
                api_key=vllm_api_key,
                model=llm_name,
            )
            return provider, llm_name

        return llm_name, factory

    raise ValueError(f"Unsupported backend '{backend}'. Use 'openrouter' or 'vllm'.")

