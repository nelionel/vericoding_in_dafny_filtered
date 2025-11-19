import argparse
import sys
import time
from openai import OpenAI

def main():
    parser = argparse.ArgumentParser(description="Chat with local vLLM model")
    parser.add_argument("--url", default="http://localhost:8000/v1", help="vLLM API base URL")
    parser.add_argument("--model", default="Qwen/Qwen3-30B-A3B-Thinking-2507", help="Model name (as served by vLLM)")
    parser.add_argument("--system", default="You are a helpful assistant.", help="System prompt")
    args = parser.parse_args()

    # Adjust model name to match the path-based serving name if necessary
    # vLLM usually serves the model using the path or the name provided.
    # We'll fetch the list of models to be sure.

    client = OpenAI(base_url=args.url, api_key="dummy")

    print(f"Connecting to {args.url}...")
    
    # Wait for server to be ready
    max_retries = 30
    model_name = args.model
    
    for i in range(max_retries):
        try:
            models = client.models.list()
            model_name = models.data[0].id
            print(f"Connected! Serving model: {model_name}")
            break
        except Exception as e:
            if i == max_retries - 1:
                print(f"Could not connect to server: {e}")
                sys.exit(1)
            time.sleep(2)
            print(".", end="", flush=True)
    print()

    messages = [{"role": "system", "content": args.system}]

    print("=== Chat Session (Type 'quit' or 'exit' to end) ===")
    while True:
        try:
            user_input = input("\nYou: ")
            if user_input.lower() in ["quit", "exit"]:
                break
            
            messages.append({"role": "user", "content": user_input})
            
            print("\nAssistant: ", end="", flush=True)
            stream = client.chat.completions.create(
                model=model_name,
                messages=messages,
                stream=True,
                temperature=0.7
            )
            
            response_content = ""
            for chunk in stream:
                if chunk.choices[0].delta.content:
                    content = chunk.choices[0].delta.content
                    print(content, end="", flush=True)
                    response_content += content
            print()
            
            messages.append({"role": "assistant", "content": response_content})
            
        except KeyboardInterrupt:
            print("\nExiting...")
            break
        except Exception as e:
            print(f"\nError: {e}")

if __name__ == "__main__":
    main()



