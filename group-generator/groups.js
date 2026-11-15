(function (root) {
  // "Ann, F" per line (gender optional). Duplicate names are rejected.
  function parseNames(text) {
    const people = [];
    const seen = new Set();
    for (const line of text.split(/\r?\n/)) {
      const [name, gender = ""] = line.split(",").map((s) => s.trim());
      if (!name) continue;
      const key = name.toLowerCase();
      if (seen.has(key)) throw new Error(`Duplicate name: ${name}`);
      seen.add(key);
      people.push({ name, gender: gender.toLowerCase() });
    }
    return people;
  }

  // "Ann, Bob" per line: the two can't share a group. Names are case-insensitive.
  function parseConflicts(text, people) {
    const known = new Set(people.map((p) => p.name.toLowerCase()));
    const pairs = [];
    for (const line of text.split(/\r?\n/)) {
      if (!line.trim()) continue;
      const [a, b] = line.split(",").map((s) => s.trim().toLowerCase());
      if (!a || !b || a === b) throw new Error(`Invalid pair: "${line.trim()}"`);
      for (const n of [a, b]) if (!known.has(n)) throw new Error(`Unknown name in pair: ${n}`);
      pairs.push([a, b]);
    }
    return pairs;
  }

  function shuffle(items, rng) {
    const a = items.slice();
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }

  // Randomised greedy placement, retried until every person fits.
  function attempt(people, groupCount, banned, mixGenders, rng) {
    const maxSize = Math.ceil(people.length / groupCount);
    const groups = Array.from({ length: groupCount }, () => []);
    for (const p of shuffle(people, rng)) {
      const key = p.name.toLowerCase();
      const options = groups
        .filter((g) => g.length < maxSize && !g.some((m) => banned.get(key)?.has(m.name.toLowerCase())))
        .map((g) => ({
          g,
          score: (mixGenders ? g.filter((m) => m.gender === p.gender).length * 1000 : 0) + g.length + rng(),
        }));
      if (!options.length) return null;
      options.sort((x, y) => x.score - y.score)[0].g.push(p);
    }
    return groups;
  }

  function generateGroups(people, groupCount, pairs, mixGenders, rng = Math.random) {
    if (!Number.isInteger(groupCount) || groupCount < 1) throw new Error("Group count must be at least 1.");
    if (groupCount > people.length) throw new Error("More groups than people.");
    const banned = new Map();
    for (const [a, b] of pairs) {
      if (!banned.has(a)) banned.set(a, new Set());
      if (!banned.has(b)) banned.set(b, new Set());
      banned.get(a).add(b);
      banned.get(b).add(a);
    }
    for (let i = 0; i < 500; i++) {
      const groups = attempt(people, groupCount, banned, mixGenders, rng);
      if (groups) return groups;
    }
    throw new Error("No valid grouping found; relax the constraints or use fewer groups.");
  }

  const api = { parseNames, parseConflicts, generateGroups };
  if (typeof module !== "undefined") module.exports = api;
  else root.GroupGenerator = api;
})(typeof self !== "undefined" ? self : this);
