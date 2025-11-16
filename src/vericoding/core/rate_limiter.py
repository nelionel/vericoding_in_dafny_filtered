"""Sliding window rate limiter for API requests."""

import threading
import time
from collections import deque
from dataclasses import dataclass


@dataclass
class RateLimiterStats:
    """Statistics for rate limiter performance."""
    
    total_requests: int
    total_wait_time: float
    max_wait_time: float
    requests_in_window: int
    limit: int
    
    @property
    def utilization(self) -> float:
        """Average utilization as a percentage (0.0 to 1.0)."""
        if self.total_requests == 0:
            return 0.0
        return self.requests_in_window / self.limit if self.limit > 0 else 0.0
    
    @property
    def avg_wait_time(self) -> float:
        """Average wait time per request in seconds."""
        return self.total_wait_time / self.total_requests if self.total_requests > 0 else 0.0


class SlidingWindowRateLimiter:
    """Thread-safe sliding window rate limiter.
    
    Tracks requests over a sliding time window and blocks when the limit would be exceeded.
    Uses a deque to efficiently track request timestamps and automatically remove old ones.
    
    Args:
        requests_per_minute: Maximum number of requests allowed per minute
        window_seconds: Size of the sliding window in seconds (default: 60)
        safety_margin: Percentage margin to stay under limit (default: 0.95 = 95%)
    """
    
    def __init__(self, requests_per_minute: int, window_seconds: int = 60, safety_margin: float = 0.95):
        self.limit = int(requests_per_minute * safety_margin)
        self.window_seconds = window_seconds
        self.request_times = deque()
        self.lock = threading.Lock()
        
        # Statistics tracking
        self.total_requests = 0
        self.total_wait_time = 0.0
        self.max_wait_time = 0.0
    
    def _clean_old_requests(self, current_time: float) -> None:
        """Remove request timestamps outside the sliding window.
        
        Must be called while holding self.lock.
        """
        cutoff_time = current_time - self.window_seconds
        while self.request_times and self.request_times[0] < cutoff_time:
            self.request_times.popleft()
    
    def _time_until_next_slot(self, current_time: float) -> float:
        """Calculate seconds to wait until a slot becomes available.
        
        Must be called while holding self.lock.
        Returns 0.0 if a slot is immediately available.
        """
        if len(self.request_times) < self.limit:
            return 0.0
        
        # Need to wait for oldest request to age out
        oldest_request = self.request_times[0]
        wait_time = (oldest_request + self.window_seconds) - current_time
        return max(0.0, wait_time)
    
    def acquire(self) -> None:
        """Acquire permission to make a request.
        
        Blocks if necessary to stay under the rate limit.
        Thread-safe and can be called from multiple threads concurrently.
        """
        while True:
            with self.lock:
                current_time = time.time()
                self._clean_old_requests(current_time)
                
                wait_time = self._time_until_next_slot(current_time)
                
                if wait_time == 0.0:
                    # Slot available, record this request and return
                    self.request_times.append(current_time)
                    self.total_requests += 1
                    return
                
                # Track wait time for statistics
                self.total_wait_time += wait_time
                self.max_wait_time = max(self.max_wait_time, wait_time)
            
            # Sleep outside the lock to allow other threads to proceed
            # Add small buffer (0.01s) to ensure we're past the window
            time.sleep(wait_time + 0.01)
    
    def get_stats(self) -> dict:
        """Get current rate limiter statistics.
        
        Returns:
            Dictionary with keys:
            - total_requests: Total number of requests made
            - requests_in_window: Current requests in the sliding window
            - limit: Configured request limit
            - utilization: Current utilization (0.0 to 1.0)
            - total_wait_time: Total seconds spent waiting
            - avg_wait_time: Average wait time per request
            - max_wait_time: Maximum wait time encountered
        """
        with self.lock:
            current_time = time.time()
            self._clean_old_requests(current_time)
            
            stats = RateLimiterStats(
                total_requests=self.total_requests,
                total_wait_time=self.total_wait_time,
                max_wait_time=self.max_wait_time,
                requests_in_window=len(self.request_times),
                limit=self.limit,
            )
            
            return {
                "total_requests": stats.total_requests,
                "requests_in_window": stats.requests_in_window,
                "limit": stats.limit,
                "utilization": stats.utilization,
                "total_wait_time": stats.total_wait_time,
                "avg_wait_time": stats.avg_wait_time,
                "max_wait_time": stats.max_wait_time,
            }


# Global rate limiter instance (singleton pattern)
_global_rate_limiter = None
_rate_limiter_lock = threading.Lock()


def get_global_rate_limiter() -> SlidingWindowRateLimiter:
    """Get or create the global rate limiter instance.
    
    This function is thread-safe and returns a singleton instance.
    The rate limiter is created on first access.
    
    Note: The rate limiter parameters are set from ProcessingConfig
    when first initialized in the evaluation script.
    """
    global _global_rate_limiter
    
    with _rate_limiter_lock:
        if _global_rate_limiter is None:
            # Default to 200 req/min if not yet configured
            # Will be properly initialized by the evaluation script
            _global_rate_limiter = SlidingWindowRateLimiter(requests_per_minute=200)
        return _global_rate_limiter


def initialize_global_rate_limiter(requests_per_minute: int, window_seconds: int = 60, safety_margin: float = 0.95) -> None:
    """Initialize the global rate limiter with specific parameters.
    
    This should be called once at the start of evaluation before any requests are made.
    
    Args:
        requests_per_minute: Maximum requests allowed per minute
        window_seconds: Size of sliding window in seconds (default: 60)
        safety_margin: Percentage of limit to use (default: 0.95 = 95%)
    """
    global _global_rate_limiter
    
    with _rate_limiter_lock:
        _global_rate_limiter = SlidingWindowRateLimiter(
            requests_per_minute=requests_per_minute,
            window_seconds=window_seconds,
            safety_margin=safety_margin,
        )


