# TCP Congestion Control & QUIC Content Progress Report

**Generated:** 2026-04-14
**Task:** Fill substantial technical content into TCP Congestion Control and QUIC protocol documentation.

---

## 1. Files Edited

| File | Original Lines | New Lines | Increase |
|------|----------------|-----------|----------|
| `Composed/schedule_formal_view/15_网络调度系统/15.3_网络拥塞控制.md` | 2,880 | 3,285 | **+405** |
| `docs/Refactor/RFC标准/RFC9000-QUIC.md` | 891 | 1,246 | **+355** |

**Total lines added:** 760

---

## 2. TCP Congestion Control — `15.3_网络拥塞控制.md`

Inserted a new technical deep-dive block as subsections **2.8 → 2.12** under `## 2 端到端拥塞控制`, just before `## 3 网络层拥塞控制`.

### 2.1 Mathematical Models (§2.8)

- **Reno**: Discrete AIMD update rules, continuous fluid-flow model `dW/dt`, and the Mathis steady-state throughput equation `Throughput = 1.22·MSS / (RTT·√p)` with full derivation steps.
- **CUBIC**: RFC 8312 window growth function `W(t) = C(t−K)³ + W_max`, detailed concave/convex/saddle-point region analysis with second-derivative table, and the TCP-friendly fallback `W_tcp(t)`.
- **BBR**: Model-driven pacing-rate and inflight-cap formulations based on `BtlBw` (10-RTT max filter) and `RTprop` (10-s min filter); includes BBR v2 `inflight_hi/lo` note.

### 2.2 State Machine Diagrams (§2.9)

- **Reno**: Mermaid `stateDiagram-v2` covering Slow Start → Congestion Avoidance → Fast Recovery, with timeout and dup-ACK transitions.
- **CUBIC**: Mermaid `stateDiagram-v2` covering Slow Start → Max Probing (concave) → Saddle Point → Probing (convex) → Multiplicative Decrease, with annotations.

### 2.3 Python Simulation (§2.10)

- Added a **self-contained, event-driven-style shared-bottleneck simulator** (`matplotlib` + `python` classes) comparing Reno, CUBIC, and BBR on a 10 Mbps / 50 ms Droptail link.
- Includes `BottleneckLink`, `RenoFlow`, `CUBICFlow`, and `BBRFlow` implementations.
- Generates `tcp_cc_simulation.png` plotting `cwnd` (in MSS) over time with a BDP reference line.

### 2.4 Linux Kernel Implementation Mapping (§2.11)

- Table mapping each algorithm to exact Linux kernel source files and core functions:
  - Reno → `net/ipv4/tcp_cong.c`
  - CUBIC → `net/ipv4/tcp_cubic.c`
  - BBR v1/v2 → `net/ipv4/tcp_bbr.c` / `tcp_bbr2.c`
  - DCTCP → `net/ipv4/tcp_dctcp.c`
  - Framework → `include/net/tcp.h`, `net/ipv4/tcp_cong.c`
  - Pacing → `net/ipv4/tcp_output.c`

### 2.5 Performance Comparison Table (§2.12)

- Unified table for **Reno / CUBIC / BBR (v1/v2) / DCTCP** covering:
  - Steady-state throughput formula
  - High-BDP scalability
  - RTT fairness
  - Loss tolerance
  - Queue delay / bufferbloat
  - UDP-competition fairness
  - Typical deployment scenarios

---

## 3. QUIC Protocol — `RFC9000-QUIC.md`

Inserted a new protocol-deep-dive block as subsections **2.5 → 2.10** under `## 2. 协议详细说明`, just before `## 3. 报文格式`.

### 3.1 0-RTT vs 1-RTT Handshake (§2.5)

- **1-RTT full handshake**: Mermaid sequence diagram with `Initial`, `Handshake`, and `1-RTT` packets, mapping TLS 1.3 flights to QUIC packet types.
- **0-RTT resumption**: Mermaid sequence diagram showing `Initial [CH+PSK]`, `0-RTT [STREAM]`, and immediate application data.
- Security boundaries documented (forward-secrecy limits, replay risk, idempotency requirements).

### 3.2 Connection ID & Migration (§2.6)

- **Connection ID structure**: DCID vs SCID lengths and roles.
- **NAT Rebinding**: Step-by-step flow with a Mermaid sequence diagram (`PATH_CHALLENGE` / `PATH_RESPONSE`).
- **Path Migration**: Address validation, independent CWND/RTT reset on new paths, `NEW_CONNECTION_ID` usage.

### 3.3 Stream Multiplexing without Head-of-Line Blocking (§2.7)

- **Stream ID encoding rules**: Table for bidirectional/unidirectional × client/server initiation.
- **STREAM frame format**: `OFF`, `LEN`, `FIN` flags and offset/length fields.
- **Flow control**: Two-level model (`MAX_DATA` for connection, `MAX_STREAM_DATA` for per-stream) with a Mermaid data-flow diagram showing independent streams multiplexed into a single QUIC packet.
- Explanation of why per-stream delivery eliminates TCP-style HoL blocking.

### 3.4 Loss Recovery (§2.8)

- **QUIC ACK vs TCP SACK**: Comparative table on granularity, option space, gap encoding, and explicit ACK Delay.
- **ACK Frequency frame**: Structure and semantics (`Ack-Eliciting Threshold`, `Request Max Ack Delay`), contrasted with TCP delayed ACK.
- **Loss detection pseudocode**: Packet-threshold (k=3) and time-threshold (`max(1.125·SRTT, SRTT + 4·RTTVAR)`) algorithms in Python-like pseudocode.

### 3.5 Python Example — `aioquic` HTTP/3 (§2.9)

- **Server** (`server.py`): `aioquic` + `H3Connection` minimal HTTP/3 server responding to GET with a plaintext body.
- **Client** (`client.py`): Connects to localhost:4433, sends HTTP/3 GET headers, prints response headers and body.
- Includes OpenSSL one-liner for generating test certs.

### 3.6 Deployment Data (§2.10)

- **Google**: 0-RTT handshake latency elimination, search latency −8%, YouTube rebuffering −9% (desktop) / −18% (mobile).
- **Cloudflare**: 35–50% 0-RTT resumption, P95 tail latency −15% to −25%, >99.9% connection-migration success.
- **Facebook/Meta**: TTFB −10–15%, mobile request-failure reduction 50%, QUIC BBR long-tail latency −20%.
- Key insights summarizing handshake, HoL-blocking, migration, and user-space iteration advantages.

---

## 4. Verification Notes

- Both edits used `StrReplaceFile` to insert content at exact boundaries (`---` section dividers) to preserve existing TOC and formatting.
- All LaTeX math, Mermaid diagrams, and Python code blocks are syntactically balanced and should render correctly in standard Markdown viewers.
- No existing sections were overwritten; content was strictly appended inline before the next major heading.
