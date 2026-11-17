# Notes for agents

## Running the benchmark

- **`make benchmark`** checks the cases of the corpus one after the other. Use it whenever the time of the checks matters: to measure speed, or for results whose times are held against those of another run. CI runs it this way.
- **`make benchmark JOBS=8`** checks eight cases at once and is several times faster. Use it when only the verdicts matter, such as to see that a change loses none. The times in its results are no more than a hint, since the checks share the machine.

## The README

Ask the user before you change `README.md`, and say what you would change and why.
