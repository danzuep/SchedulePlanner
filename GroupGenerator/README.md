# Group Generator

A dependency-free page that splits a list of unique names into groups.

- Enter names, one per line, with an optional gender (`Ann, F`).
- Choose the number of groups.
- List pairs that can't share a group (`Ann, Bob`).
- Optionally mix genders evenly.

Open `index.html` in a browser (keep `groups.js` beside it). Run tests with `node --test`.
CI uploads `index.html` and `groups.js` as the `group-generator` artifact.
