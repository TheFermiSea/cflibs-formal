#!/usr/bin/env python3
"""Cache-busted throughput measurement for a llama-server endpoint (spec 04 §10).

Repeated identical prompts inflate llama.cpp's numbers (prompt cache hits, n-gram/MTP
speculation on familiar text). Every request here carries a unique random preamble, sends
`cache_prompt: false`, and asks for a long free-text answer so `predicted_n` is large enough
for `predicted_per_second` to mean something. Reports the server's own `timings` block per
request and the median across requests.

usage: bench_cachebust.py URL [--n 3] [--max-tokens 400] [--model NAME] [--reasoning high]
"""
import argparse, json, secrets, statistics, sys, time, urllib.request

PROMPTS = [
    "Explain, in prose, how the Saha equation couples the ionization fractions of a plasma to its "
    "electron density and temperature, and why the coupling makes charge neutrality a fixed-point problem.",
    "Describe the difference between a Lorentzian and a Gaussian line profile, how their widths add "
    "under convolution, and why the Voigt profile has no closed form in elementary functions.",
    "Explain what it means for a linear inverse problem to be well-posed, and how the kernel of the "
    "forward matrix determines whether a composition can be recovered from a spectrum.",
    "Summarize how a calibration-free LIBS analysis estimates plasma temperature from a Boltzmann plot "
    "and where the main systematic errors enter.",
]


def one(url, model, max_tokens, i, reasoning):
    body = {
        "model": model,
        "messages": [{"role": "user", "content": f"[run {secrets.token_hex(8)}] {PROMPTS[i % len(PROMPTS)]}"}],
        "max_tokens": max_tokens,
        "temperature": 0.7,
        "seed": secrets.randbelow(2**31),
        "cache_prompt": False,
    }
    if reasoning:
        body["chat_template_kwargs"] = {"reasoning_effort": reasoning}
    req = urllib.request.Request(url.rstrip("/") + "/v1/chat/completions",
                                 data=json.dumps(body).encode(), headers={"Content-Type": "application/json"})
    t0 = time.time()
    with urllib.request.urlopen(req, timeout=1800) as r:
        d = json.load(r)
    wall = time.time() - t0
    t = d.get("timings", {})
    return {"prompt_n": t.get("prompt_n"), "cache_n": t.get("cache_n"), "predicted_n": t.get("predicted_n"),
            "prompt_tps": t.get("prompt_per_second"), "decode_tps": t.get("predicted_per_second"),
            "wall_s": round(wall, 1), "finish": d["choices"][0]["finish_reason"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("url"); ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--max-tokens", type=int, default=400); ap.add_argument("--model", default="leanstral")
    ap.add_argument("--reasoning", default=None, help="chat_template_kwargs.reasoning_effort, e.g. high")
    a = ap.parse_args()
    rows = [one(a.url, a.model, a.max_tokens, i, a.reasoning) for i in range(a.n)]
    for r in rows:
        print(json.dumps(r))
    dec = [r["decode_tps"] for r in rows if r["decode_tps"]]
    pp = [r["prompt_tps"] for r in rows if r["prompt_tps"]]
    if any((r["cache_n"] or 0) > 0 for r in rows):
        print("WARNING: cache_n > 0 on some request; numbers are not cache-busted", file=sys.stderr)
    print(f"median decode tok/s = {statistics.median(dec):.1f}   median prompt tok/s = {statistics.median(pp):.1f}   n = {len(rows)}")


if __name__ == "__main__":
    main()
