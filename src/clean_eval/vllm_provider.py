"""Simple OpenAI-compatible provider for local vLLM servers."""

from __future__ import annotations

import openai

from vericoding.core.llm_providers import (
    LLMProvider,
    LLMResponse,
    RateLimitExceededError,
)


class VLLMProvider(LLMProvider):
    """Wraps the vLLM OpenAI-compatible HTTP server."""

    def __init__(
        self,
        base_url: str,
        api_key: str,
        model: str,
        **kwargs,
    ):
        super().__init__(api_key or "dummy", model, **kwargs)
        self.client = openai.OpenAI(api_key=api_key, base_url=base_url)

    def call_api(self, prompt: str) -> LLMResponse:
        from vericoding.core.llm_providers import _build_messages
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=_build_messages(prompt, self.model),
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )
        except openai.RateLimitError as exc:
            raise RateLimitExceededError(str(exc)) from exc

        if not response.choices:
            raise ValueError("Empty response from vLLM server")

        text = response.choices[0].message.content or ""
        input_tokens = getattr(response.usage, "prompt_tokens", 0)
        output_tokens = getattr(response.usage, "completion_tokens", 0)

        return LLMResponse(text=text, input_tokens=input_tokens, output_tokens=output_tokens)

    def get_required_env_var(self) -> str:  # pragma: no cover - configuration helper
        return "VLLM_API_KEY"

