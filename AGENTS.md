# Agent instructions

- Work on `main` and push it directly: every push to `main` deploys the playground to GitHub Pages (after its browser tests), and that is how the user tests changes (the user's decision, 2026-10-02). The `agent` branch is not used anymore.
- Append short, timestamped, factual entries to `lab-notes.md` for meaningful commands, decisions, and outcomes.
- After each logically complete unit of work, commit the changes, update `lab-notes.md` with the result and commit, and push `main` to `origin` -- so the change gets deployed, and an interrupted SLURM session loses as little work as possible.
- Before ending a task, commit and push all intended work and add a final summary entry to `lab-notes.md`.

