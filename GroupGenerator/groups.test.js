const test = require("node:test");
const assert = require("node:assert");
const { parseNames, parseConflicts, generateGroups } = require("./groups.js");

const people = parseNames("Ann, F\nBob, M\nCam, F\nDan, M\nEve, F\nFay, F\nGus, M\nHal, M");

test("rejects duplicate names", () => {
  assert.throws(() => parseNames("Ann\nann"), /Duplicate/);
});

test("rejects unknown names in pairs", () => {
  assert.throws(() => parseConflicts("Ann, Zed", people), /Unknown/);
});

test("conflicting pairs are never grouped together", () => {
  const pairs = parseConflicts("Ann, Bob\nCam, Dan\nEve, Fay", people);
  for (let i = 0; i < 100; i++) {
    for (const g of generateGroups(people, 2, pairs, false)) {
      const names = g.map((p) => p.name);
      for (const [a, b] of [["Ann", "Bob"], ["Cam", "Dan"], ["Eve", "Fay"]])
        assert.ok(!(names.includes(a) && names.includes(b)));
    }
  }
});

test("groups are even in size and genders are mixed", () => {
  for (let i = 0; i < 100; i++) {
    const groups = generateGroups(people, 2, [], true);
    assert.deepStrictEqual(groups.map((g) => g.length), [4, 4]);
    for (const g of groups) assert.strictEqual(g.filter((p) => p.gender === "m").length, 2);
  }
});

test("uneven sizes differ by at most one", () => {
  const sizes = generateGroups(people, 3, [], false).map((g) => g.length).sort();
  assert.deepStrictEqual(sizes, [2, 3, 3]);
});

test("impossible constraints throw", () => {
  const two = parseNames("A\nB");
  assert.throws(() => generateGroups(two, 1, parseConflicts("A, B", two), false), /No valid/);
});
