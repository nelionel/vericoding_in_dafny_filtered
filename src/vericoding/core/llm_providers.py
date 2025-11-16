"""LLM provider abstractions and implementations."""

import os
import threading
from abc import ABC, abstractmethod
from time import time, sleep
from dataclasses import dataclass
from .config import ProcessingConfig

import anthropic
import openai


class RateLimitExceededError(Exception):
    """Raised when a provider reports a rate limit error."""



@dataclass
class LLMResponse:
    """Response from LLM API including token usage information."""

    text: str
    input_tokens: int = 0
    output_tokens: int = 0


class LLMProvider(ABC):
    """Abstract interface for LLM providers."""

    def __init__(
        self, api_key: str, model: str, max_tokens: int = 16384, timeout: float = 60.0
    ):
        self.api_key = api_key
        self.model = model
        self.max_tokens = max_tokens
        self.timeout = timeout

    @abstractmethod
    def call_api(self, prompt: str) -> LLMResponse:
        """Call the LLM API with the given prompt."""
        pass

    @abstractmethod
    def get_required_env_var(self) -> str:
        """Return the required environment variable name for API key."""
        pass


def _build_messages(prompt: str, model: str) -> list[dict[str, str]]:
    """Construct chat payloads, inserting Harmony system prompt for GPT-OSS."""
    messages = [{"role": "user", "content": prompt}]

    if "gpt-oss" in model:
        system_prompt = (
            "You are an expert formal methods assistant.\n"
            "Reasoning: high\n"
            "Follow the Harmony response format strictly."
        )
        messages.insert(0, {"role": "system", "content": system_prompt})

    return messages


class AnthropicProvider(LLMProvider):
    """Anthropic Claude LLM provider."""

    def __init__(self, api_key: str, model: str = "claude-sonnet-4-20250514", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = anthropic.Anthropic(api_key=api_key)

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                messages=[{"role": "user", "content": prompt}],
                timeout=self.timeout,
            )

            if response.content and len(response.content) > 0:
                text_content = response.content[0]
                text = (
                    text_content.text
                    if hasattr(text_content, "text")
                    else str(text_content)
                )
                if not text or not str(text).strip():
                    raise ValueError("Empty response from Anthropic API")

                # Extract token usage
                input_tokens = (
                    getattr(response.usage, "input_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )
                output_tokens = (
                    getattr(response.usage, "output_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )

                return LLMResponse(
                    text=text, input_tokens=input_tokens, output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from Claude API")

        except anthropic.RateLimitError as e:
            raise RateLimitExceededError(str(e)) from e
        except anthropic.APIError as e:
            raise ValueError(f"Anthropic API error: {str(e)}")
        except Exception as e:
            raise ValueError(f"Error calling Claude API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "ANTHROPIC_API_KEY"


class OpenAIProvider(LLMProvider):
    """OpenAI GPT LLM provider."""

    def __init__(self, api_key: str, model: str = "gpt-4o", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(api_key=api_key)

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=_build_messages(prompt, self.model),
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from OpenAI API")

                # Extract token usage
                input_tokens = (
                    getattr(response.usage, "prompt_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )
                output_tokens = (
                    getattr(response.usage, "completion_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )

                return LLMResponse(
                    text=text, input_tokens=input_tokens, output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from OpenAI API")

        except openai.RateLimitError as e:
            raise RateLimitExceededError(str(e)) from e
        except Exception as e:
            raise ValueError(f"Error calling OpenAI API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "OPENAI_API_KEY"


class DeepSeekProvider(LLMProvider):
    """DeepSeek LLM provider."""

    def __init__(self, api_key: str, model: str = "deepseek-chat", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(
            api_key=api_key, base_url="https://api.deepseek.com"
        )

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=_build_messages(prompt, self.model),
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from DeepSeek API")

                # Extract token usage (DeepSeek uses OpenAI-compatible format)
                input_tokens = (
                    getattr(response.usage, "prompt_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )
                output_tokens = (
                    getattr(response.usage, "completion_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )

                return LLMResponse(
                    text=text, input_tokens=input_tokens, output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from DeepSeek API")

        except openai.RateLimitError as e:
            raise RateLimitExceededError(str(e)) from e
        except Exception as e:
            raise ValueError(f"Error calling DeepSeek API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "DEEPSEEK_API_KEY"


class GrokProvider(LLMProvider):
    """Grok (xAI) LLM provider."""

    def __init__(self, api_key: str, model: str = "grok-4", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=_build_messages(prompt, self.model),
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from Grok API")

                # Extract token usage (Grok uses OpenAI-compatible format)
                input_tokens = (
                    getattr(response.usage, "prompt_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )
                output_tokens = (
                    getattr(response.usage, "completion_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )

                return LLMResponse(
                    text=text, input_tokens=input_tokens, output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from Grok API")

        except openai.RateLimitError as e:
            raise RateLimitExceededError(str(e)) from e
        except Exception as e:
            raise ValueError(f"Error calling Grok API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "XAI_API_KEY"


class OpenRouterProvider(LLMProvider):
    """OpenRouter LLM provider."""

    def __init__(self, api_key: str, model: str = "openai/gpt-4o", reasoning_config: dict | None = None, **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.reasoning_config = reasoning_config
        try:
            import openai

            self.client = openai.OpenAI(
                api_key=api_key, base_url="https://openrouter.ai/api/v1"
            )
        except ImportError:
            raise ImportError("OpenAI package not installed")

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            # Build request kwargs
            kwargs = {
                "model": self.model,
                "messages": _build_messages(prompt, self.model),
                "max_tokens": self.max_tokens,
                "timeout": self.timeout,
            }

            # Add reasoning parameters if configured
            if self.reasoning_config:
                kwargs["extra_body"] = {"reasoning": self.reasoning_config}
            
            response = self.client.chat.completions.create(**kwargs)

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from OpenRouter API")

                # Extract token usage (OpenRouter uses OpenAI-compatible format)
                input_tokens = (
                    getattr(response.usage, "prompt_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )
                output_tokens = (
                    getattr(response.usage, "completion_tokens", 0)
                    if hasattr(response, "usage")
                    else 0
                )

                return LLMResponse(
                    text=text, input_tokens=input_tokens, output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from OpenRouter API")

        except openai.RateLimitError as e:
            raise RateLimitExceededError(str(e)) from e
        except Exception as e:
            raise ValueError(f"Error calling OpenRouter API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "OPENROUTER_API_KEY"


def create_llm_provider(llm_name: str) -> tuple[LLMProvider, str]:
    """Factory function to create LLM providers.

    Args:
        llm_name: Name of the LLM (e.g., 'claude-sonnet', 'gpt', 'claude-direct')

    Returns:
        tuple[LLMProvider, str]: The provider instance and the resolved model name.
    """
    import sys

    provider_configs = {
        "claude-sonnet": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-sonnet-4",
            "env_var": "OPENROUTER_API_KEY",
        },
        "claude-4.5-sonnet": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-sonnet-4.5",
            "env_var": "OPENROUTER_API_KEY",
            "reasoning": {"max_tokens": 8192},
        },
        "claude-opus": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-opus-4.1",
            "env_var": "OPENROUTER_API_KEY",
        },
        "gpt": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-5",  # Latest GPT-5 (Aug 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "gpt-oss-20b": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-oss-20b",
            "env_var": "OPENROUTER_API_KEY",
            "reasoning": {"effort": "high"},
        },
        "gpt-mini": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-5-mini",
            "env_var": "OPENROUTER_API_KEY",
        },
        "gpt-5-codex": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-5-codex",
            "env_var": "OPENROUTER_API_KEY",
        },
        "o1": {
            "class": OpenRouterProvider,
            "default_model": "openai/o1-preview",  # O1 reasoning model
            "env_var": "OPENROUTER_API_KEY",
        },
        "gemini": {
            "class": OpenRouterProvider,
            "default_model": "google/gemini-2.5-pro",  # Latest Gemini 2.5 Pro (June 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "gemini-flash": {
            "class": OpenRouterProvider,
            "default_model": "google/gemini-2.5-flash",  # Gemini 2.5 Flash (August 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "grok": {
            "class": OpenRouterProvider,
            "default_model": "x-ai/grok-4",  # Latest Grok 4 (July 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "grok-code": {
            "class": OpenRouterProvider,
            "default_model": "x-ai/grok-code-fast-1",
            "env_var": "OPENROUTER_API_KEY",
        },
        "deepseek": {
            "class": OpenRouterProvider,
            "default_model": "deepseek/deepseek-chat-v3.1",  # Latest DeepSeek V3
            "env_var": "OPENROUTER_API_KEY",
        },
        "glm": {
            "class": OpenRouterProvider,
            "default_model": "z-ai/glm-4.5",  # GLM-4.5 (2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "mistral-medium": {
            "class": OpenRouterProvider,
            "default_model": "mistralai/mistral-medium-3.1",
            "env_var": "OPENROUTER_API_KEY",
        },
        "mistral-codestral": {
            "class": OpenRouterProvider,
            "default_model": "mistralai/codestral-2508",
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwen-thinking": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwen3-30b-a3b-thinking-2507",
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwen-coder": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwen3-coder-30b-a3b-instruct",
            "env_var": "OPENROUTER_API_KEY",
        },
        # Reasoning-enabled models for vericoding benchmark
        "o4-mini": {
            "class": OpenRouterProvider,
            "default_model": "openai/o4-mini",
            "env_var": "OPENROUTER_API_KEY",
            "reasoning": {"effort": "high"},
        },
        "claude-haiku": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-haiku-4.5",
            "env_var": "OPENROUTER_API_KEY",
            "reasoning": {"max_tokens": 8192},
        },
        # Additional models for evaluation
        "mistral-small": {
            "class": OpenRouterProvider,
            "default_model": "mistralai/mistral-small-3.2-24b-instruct",  # Paid version - free tier has capacity issues
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwq-32b": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwq-32b",
            "env_var": "OPENROUTER_API_KEY",
            # QwQ is a reasoning model, may need reasoning config - test without first
        },
        "gemma-27b": {
            "class": OpenRouterProvider,
            "default_model": "google/gemma-3-27b-it",  # Paid version - free tier has broken token tracking
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwen3-30b-thinking": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwen3-30b-a3b-thinking-2507",
            "env_var": "OPENROUTER_API_KEY",
            # Note: Has "thinking" in model name, may support reasoning
        },
        "gemma-12b": {
            "class": OpenRouterProvider,
            "default_model": "google/gemma-3-12b-it",  # Paid version - free tier has broken token tracking
            "env_var": "OPENROUTER_API_KEY",
        },
        # Keep legacy direct providers for backwards compatibility
        "openai-direct": {
            "class": OpenAIProvider,
            "default_model": "gpt-4o",
            "env_var": "OPENAI_API_KEY",
        },
        "claude-direct": {
            "class": AnthropicProvider,
            "default_model": "claude-sonnet-4-20250514",
            "env_var": "ANTHROPIC_API_KEY",
        },
        "grok-direct": {
            "class": GrokProvider,
            "default_model": "grok-4",
            "env_var": "XAI_API_KEY",
        },
        # Legacy aliases for backwards compatibility
        "claude": {
            "class": AnthropicProvider,
            "default_model": "claude-sonnet-4-20250514",
            "env_var": "ANTHROPIC_API_KEY",
        },
        "openai": {
            "class": OpenAIProvider,
            "default_model": "gpt-4o",
            "env_var": "OPENAI_API_KEY",
        },
    }

    if llm_name not in provider_configs:
        available = ", ".join(provider_configs.keys())
        print(f"Error: Unsupported LLM: {llm_name}. Available: {available}")
        sys.exit(1)

    config = provider_configs[llm_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var)

    if not api_key:
        print(
            f"Error: {env_var} environment variable is required for {llm_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key\n"
            f"\nNote: .env files are automatically loaded if they exist in the current or parent directory."
        )
        sys.exit(1)

    selected_model = config["default_model"]
    
    # Pass reasoning config if present (for OpenRouterProvider)
    reasoning_config = config.get("reasoning")
    if reasoning_config:
        provider = config["class"](api_key, selected_model, reasoning_config=reasoning_config)
    else:
        provider = config["class"](api_key, selected_model)
    
    # Note: Don't print here - causes noise with parallel workers
    # The calling script (run_hard_subset_eval.py) will print model info
    return provider, selected_model


# Global token counter for tracking across all calls (thread-safe)
_global_token_stats = {"input_tokens": 0, "output_tokens": 0, "total_calls": 0}
_token_stats_lock = threading.Lock()

# Global step counter for W&B logging (step = 1 API call)
_global_step_counter = {"step": 0, "problems_processed": 0}
_step_counter_lock = threading.Lock()


def increment_step() -> int:
    """Increment and return the global step counter (thread-safe)."""
    with _step_counter_lock:
        _global_step_counter["step"] += 1
        return _global_step_counter["step"]


def increment_problems_processed() -> int:
    """Increment and return the problems processed counter (thread-safe)."""
    with _step_counter_lock:
        _global_step_counter["problems_processed"] += 1
        return _global_step_counter["problems_processed"]


def get_problems_processed() -> int:
    """Get current count of problems processed (thread-safe)."""
    with _step_counter_lock:
        return _global_step_counter["problems_processed"]


def get_global_token_stats() -> dict:
    """Get the current global token usage statistics."""
    with _token_stats_lock:
        return _global_token_stats.copy()


def reset_global_token_stats():
    """Reset the global token usage statistics."""
    with _token_stats_lock:
        _global_token_stats["input_tokens"] = 0
        _global_token_stats["output_tokens"] = 0
        _global_token_stats["total_calls"] = 0


_RATE_LIMIT_MAX_RETRIES = int(os.getenv("VERICODING_RATE_LIMIT_MAX_RETRIES", "5"))
_RATE_LIMIT_BACKOFF_BASE = float(os.getenv("VERICODING_RATE_LIMIT_BACKOFF_BASE", "1.0"))
_RATE_LIMIT_BACKOFF_MAX = float(os.getenv("VERICODING_RATE_LIMIT_BACKOFF_MAX", "30.0"))


def call_llm_detailed(
    provider: LLMProvider, config: ProcessingConfig, prompt: str, wandb=None
) -> dict:
    """Call LLM with rate limiting and return full metadata including tokens/cost.
    
    Returns:
        dict with keys:
        - text: The response text
        - input_tokens: Number of input tokens
        - output_tokens: Number of output tokens
        - llm_duration_sec: Time spent in LLM call
        - cost_usd: Estimated cost in USD
    """
    # Use dynamic rate limiting if enabled, otherwise use fixed delay
    if config.use_dynamic_rate_limit:
        from .rate_limiter import get_global_rate_limiter
        rate_limiter = get_global_rate_limiter()
        rate_limiter.acquire()  # Block if needed to stay under rate limit
    else:
        # Legacy fixed delay
        sleep(config.api_rate_limit_delay)
    
    attempt = 0
    while True:
        start = time()
        try:
            llm_response = provider.call_api(prompt)
            llm_duration_sec = time() - start
            break
        except RateLimitExceededError:
            if attempt >= _RATE_LIMIT_MAX_RETRIES:
                raise
            wait_time = min(
                _RATE_LIMIT_BACKOFF_BASE * (2 ** attempt),
                _RATE_LIMIT_BACKOFF_MAX,
            )
            if config.debug_mode:
                print(
                    f"Rate limit hit for {getattr(provider, 'model', 'unknown')} - "
                    f"retrying in {wait_time:.1f}s ({attempt + 1}/{_RATE_LIMIT_MAX_RETRIES})"
                )
            sleep(wait_time)
            attempt += 1
            continue
    latency_ms = llm_duration_sec * 1000

    # Update global token statistics (thread-safe)
    with _token_stats_lock:
        _global_token_stats["input_tokens"] += llm_response.input_tokens
        _global_token_stats["output_tokens"] += llm_response.output_tokens
        _global_token_stats["total_calls"] += 1

    # Calculate cost (pricing per million tokens)
    # These are approximate - actual costs may vary by provider
    pricing_map = {
        "openai/o4-mini": {"input": 1.10, "output": 4.40},
        "anthropic/claude-sonnet-4.5": {"input": 3.00, "output": 15.00},
        "anthropic/claude-haiku-4.5": {"input": 1.00, "output": 5.00},
    }
    model_id = getattr(provider, "model", "")
    pricing = pricing_map.get(model_id, {"input": 0, "output": 0})
    cost_usd = (llm_response.input_tokens * pricing["input"] / 1_000_000) + \
               (llm_response.output_tokens * pricing["output"] / 1_000_000)

    # Increment step counter (step = 1 successful API call)
    current_step = increment_step()
    problems_so_far = get_problems_processed()

    if wandb and hasattr(wandb, "log") and hasattr(wandb, "run") and wandb.run:
        try:
            # Log the 5 required step-based metrics as line graphs
            wandb.log({
                # Step-based metrics (x-axis is implicit via log order)
                "step_metrics/time_per_step": llm_duration_sec,
                "step_metrics/problems_processed_per_step": problems_so_far,
                "step_metrics/cost_per_step": cost_usd,
                "step_metrics/tokens_in_per_step": llm_response.input_tokens,
                "step_metrics/tokens_out_per_step": llm_response.output_tokens,
                # Explicit step number for reference
                "step_metrics/step_number": current_step,
            })
        except Exception as e:
            print(f"There was a W&B error {e} in llm_providers.py")

    return {
        "text": llm_response.text,
        "input_tokens": llm_response.input_tokens,
        "output_tokens": llm_response.output_tokens,
        "llm_duration_sec": llm_duration_sec,
        "cost_usd": cost_usd,
    }


def call_llm(
    provider: LLMProvider, config: ProcessingConfig, prompt: str, wandb=None
) -> str:
    """Call LLM with rate limiting and optional wandb logging.
    
    This is a legacy wrapper that returns only the text.
    For detailed metrics, use call_llm_detailed() instead.
    """
    result = call_llm_detailed(provider, config, prompt, wandb)
    return result["text"]
