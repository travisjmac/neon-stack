/**
 * Neon Stack
 * Falling-block puzzle. No dependencies.
 * Music: "Neon Sign Circuit" by MintoDog. License: CC0.
 */
(function () {
  "use strict";

  const COLS = 10;
  const ROWS = 20;
  const SPAWN_X = 3;
  const SPAWN_Y = 0;
  const IDS = ["I", "O", "T", "S", "Z", "J", "L"];

  const COLORS = {
    I: "#00f0ff",
    O: "#ffe600",
    T: "#ff2bd6",
    S: "#39ff14",
    Z: "#ff3b3b",
    J: "#2f6bff",
    L: "#c24bff",
  };

  const LINE_POINTS = [0, 100, 300, 500, 800];
  const CLEAR_NAME = ["", "Single", "Double", "Triple", "Nova"];
  const COMBO_STEP = 50;
  const SOFT_POINT = 1;
  const HARD_POINT = 2;

  const DAS_MS = 150;
  const ARR_MS = 30;
  const SOFT_MS = 45;
  const LOCK_MS = 480;
  const MAX_LOCK_RESETS = 14;
  const CLEAR_MS = 360;

  const KICKS = [
    [0, 0],
    [-1, 0],
    [1, 0],
    [-2, 0],
    [2, 0],
    [0, -1],
    [-1, -1],
    [1, -1],
    [0, -2],
    [-2, -1],
    [2, -1],
  ];

  function rotateCW(matrix) {
    const n = matrix.length;
    const out = [];
    for (let r = 0; r < n; r++) out.push(new Array(n).fill(0));
    for (let r = 0; r < n; r++) {
      for (let c = 0; c < n; c++) out[c][n - 1 - r] = matrix[r][c];
    }
    return out;
  }

  function rotationsFor(id, base) {
    if (id === "O") return [base, base, base, base];
    const rots = [base];
    for (let i = 0; i < 3; i++) rots.push(rotateCW(rots[i]));
    return rots;
  }

  const BASE = {
    I: [
      [0, 0, 0, 0],
      [1, 1, 1, 1],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    O: [
      [0, 1, 1, 0],
      [0, 1, 1, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    T: [
      [0, 1, 0, 0],
      [1, 1, 1, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    S: [
      [0, 1, 1, 0],
      [1, 1, 0, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    Z: [
      [1, 1, 0, 0],
      [0, 1, 1, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    J: [
      [1, 0, 0, 0],
      [1, 1, 1, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
    L: [
      [0, 0, 1, 0],
      [1, 1, 1, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 0],
    ],
  };

  const ROTATIONS = {};
  IDS.forEach(function (id) {
    ROTATIONS[id] = rotationsFor(id, BASE[id]);
  });

  function cellsOf(piece) {
    const matrix = ROTATIONS[piece.id][piece.rot & 3];
    const out = [];
    for (let r = 0; r < 4; r++) {
      for (let c = 0; c < 4; c++) {
        if (matrix[r][c]) out.push([piece.x + c, piece.y + r]);
      }
    }
    return out;
  }

  function dropMs(level) {
    return Math.max(60, Math.floor(800 * Math.pow(0.78, level - 1)));
  }

  function shuffled(list) {
    const copy = list.slice();
    for (let i = copy.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const tmp = copy[i];
      copy[i] = copy[j];
      copy[j] = tmp;
    }
    return copy;
  }

  function createSession(options) {
    const forced = options && options.pieces ? options.pieces.slice() : null;
    let board = [];
    let bag = [];
    let queue = [];
    let current = null;
    let holdId = null;
    let holdLocked = false;
    let score = 0;
    let lines = 0;
    let level = 1;
    let streak = 0;
    let status = "playing";
    let resumeTo = "playing";
    let clearingRows = [];
    let clearAcc = 0;
    let lockAcc = 0;
    let lockResets = 0;
    let gravAcc = 0;
    let softAcc = 0;
    let dasAcc = 0;
    let arrAcc = 0;
    let horiz = 0;
    let skipLock = false;
    let banner = null;
    const held = { left: false, right: false, soft: false };

    function emptyBoard() {
      const next = [];
      for (let y = 0; y < ROWS; y++) next.push(new Array(COLS).fill(null));
      return next;
    }

    function fits(piece) {
      const cells = cellsOf(piece);
      for (let i = 0; i < cells.length; i++) {
        const x = cells[i][0];
        const y = cells[i][1];
        if (x < 0 || x >= COLS || y < 0 || y >= ROWS) return false;
        if (board[y][x]) return false;
      }
      return true;
    }

    function shifted(piece, dx, dy, rot) {
      return {
        id: piece.id,
        rot: rot === undefined ? piece.rot : rot,
        x: piece.x + dx,
        y: piece.y + dy,
      };
    }

    function signature(piece) {
      return cellsOf(piece)
        .map(function (cell) { return cell[0] + ":" + cell[1]; })
        .sort()
        .join("|");
    }

    function take() {
      if (forced && forced.length) return forced.shift();
      if (!bag.length) bag = shuffled(IDS);
      return bag.pop();
    }

    function spawn() {
      const id = queue.shift();
      queue.push(take());
      current = { id: id, rot: 0, x: SPAWN_X, y: SPAWN_Y };
      holdLocked = false;
      lockAcc = 0;
      lockResets = 0;
      gravAcc = 0;
      softAcc = 0;
      if (!fits(current)) {
        current = null;
        status = "gameover";
      }
    }

    function reset() {
      board = emptyBoard();
      bag = [];
      queue = [];
      current = null;
      holdId = null;
      holdLocked = false;
      score = 0;
      lines = 0;
      level = 1;
      streak = 0;
      status = "playing";
      resumeTo = "playing";
      clearingRows = [];
      clearAcc = 0;
      lockAcc = 0;
      lockResets = 0;
      gravAcc = 0;
      softAcc = 0;
      dasAcc = 0;
      arrAcc = 0;
      horiz = 0;
      skipLock = false;
      banner = null;
      held.left = false;
      held.right = false;
      held.soft = false;
      if (forced) {
        forced.splice(0, forced.length);
        if (options && options.pieces) {
          for (let i = 0; i < options.pieces.length; i++) forced.push(options.pieces[i]);
        }
      }
      while (queue.length < 5) queue.push(take());
      spawn();
    }

    function award(count) {
      if (count <= 0) {
        streak = 0;
        return;
      }
      const linePts = LINE_POINTS[count] * level;
      streak += 1;
      const comboPts = streak >= 2 ? COMBO_STEP * (streak - 1) * level : 0;
      score += linePts + comboPts;
      lines += count;
      const nextLevel = 1 + Math.floor(lines / 10);
      let detail = "";
      if (streak >= 2) detail = "Combo " + streak;
      if (nextLevel > level) {
        detail = detail ? detail + " · Level " + nextLevel : "Level " + nextLevel;
        level = nextLevel;
      }
      banner = {
        title: CLEAR_NAME[count] + " +" + (linePts + comboPts),
        detail: detail,
        life: 1200,
      };
    }

    function fullRows() {
      const rows = [];
      for (let y = 0; y < ROWS; y++) {
        let full = true;
        for (let x = 0; x < COLS; x++) {
          if (!board[y][x]) {
            full = false;
            break;
          }
        }
        if (full) rows.push(y);
      }
      return rows;
    }

    function lockPiece() {
      if (!current || status !== "playing") return;
      const piece = current;
      current = null;
      const cells = cellsOf(piece);
      for (let i = 0; i < cells.length; i++) {
        board[cells[i][1]][cells[i][0]] = piece.id;
      }
      const rows = fullRows();
      if (rows.length) {
        award(rows.length);
        clearingRows = rows;
        clearAcc = 0;
        status = "clearing";
        return;
      }
      award(0);
      spawn();
    }

    function finishClear() {
      const drop = {};
      for (let i = 0; i < clearingRows.length; i++) drop[clearingRows[i]] = true;
      const next = [];
      for (let y = 0; y < ROWS; y++) {
        if (!drop[y]) next.push(board[y]);
      }
      while (next.length < ROWS) next.unshift(new Array(COLS).fill(null));
      board = next;
      clearingRows = [];
      status = "playing";
      spawn();
    }

    function afterPlayerMove() {
      if (!current) return;
      if (!fits(shifted(current, 0, 1))) {
        if (lockResets < MAX_LOCK_RESETS) {
          lockAcc = 0;
          lockResets += 1;
          skipLock = true;
        }
      } else {
        lockAcc = 0;
        lockResets = 0;
      }
    }

    function tryMove(dx, dy, player) {
      if (status !== "playing" || !current) return false;
      const next = shifted(current, dx, dy);
      if (!fits(next)) return false;
      current = next;
      if (player && dy > 0) score += SOFT_POINT;
      if (player) afterPlayerMove();
      else if (fits(shifted(current, 0, 1))) lockAcc = 0;
      return true;
    }

    function rotate(dir) {
      if (status !== "playing" || !current) return false;
      const nextRot = (current.rot + dir + 4) % 4;
      for (let i = 0; i < KICKS.length; i++) {
        const kick = KICKS[i];
        const candidate = shifted(current, kick[0], kick[1], nextRot);
        if (!fits(candidate)) continue;
        const changed = signature(current) !== signature(candidate);
        current = candidate;
        if (changed) afterPlayerMove();
        return true;
      }
      return false;
    }

    function hardDrop() {
      if (status !== "playing" || !current) return;
      let dist = 0;
      while (fits(shifted(current, 0, 1))) {
        current = shifted(current, 0, 1);
        dist += 1;
      }
      if (dist) score += dist * HARD_POINT;
      lockPiece();
    }

    function doHold() {
      if (status !== "playing" || !current || holdLocked) return;
      const incoming = holdId;
      holdId = current.id;
      if (!incoming) {
        spawn();
        holdLocked = true;
        return;
      }
      current = { id: incoming, rot: 0, x: SPAWN_X, y: SPAWN_Y };
      holdLocked = true;
      lockAcc = 0;
      lockResets = 0;
      gravAcc = 0;
      softAcc = 0;
      if (!fits(current)) {
        current = null;
        status = "gameover";
      }
    }

    function startHoriz(dir, moveNow) {
      horiz = dir;
      dasAcc = 0;
      arrAcc = 0;
      if (moveNow && status === "playing") tryMove(dir, 0, true);
    }

    function press(action) {
      if (action === "restart") {
        reset();
        return;
      }
      if (action === "quit") {
        status = "stopped";
        held.left = false;
        held.right = false;
        held.soft = false;
        horiz = 0;
        return;
      }
      if (action === "pause") {
        if (status === "playing" || status === "clearing") {
          resumeTo = status;
          status = "paused";
        } else if (status === "paused") {
          status = resumeTo || "playing";
        }
        return;
      }
      if (action === "left" || action === "right" || action === "soft") held[action] = true;
      if (action === "left") startHoriz(-1, true);
      else if (action === "right") startHoriz(1, true);
      if (status !== "playing") return;
      if (action === "soft") tryMove(0, 1, true);
      else if (action === "hard") hardDrop();
      else if (action === "cw") rotate(1);
      else if (action === "ccw") rotate(-1);
      else if (action === "hold") doHold();
    }

    function release(action) {
      if (action !== "left" && action !== "right" && action !== "soft") return;
      held[action] = false;
      if (action === "left" || action === "right") {
        if (held.left && !held.right) startHoriz(-1, status === "playing");
        else if (held.right && !held.left) startHoriz(1, status === "playing");
        else if (!held.left && !held.right) horiz = 0;
      }
    }

    function tick(dt) {
      if (status === "paused" || status === "stopped" || status === "gameover") return;
      if (banner) {
        banner.life -= dt;
        if (banner.life <= 0) banner = null;
      }
      if (status === "clearing") {
        clearAcc += dt;
        if (clearAcc >= CLEAR_MS) finishClear();
        return;
      }
      if (horiz !== 0) {
        dasAcc += dt;
        if (dasAcc >= DAS_MS) {
          arrAcc += dt;
          while (arrAcc >= ARR_MS) {
            arrAcc -= ARR_MS;
            if (!tryMove(horiz, 0, true)) break;
          }
        }
      }
      if (current && held.soft) {
        softAcc += dt;
        while (softAcc >= SOFT_MS) {
          softAcc -= SOFT_MS;
          if (!tryMove(0, 1, true)) break;
        }
      } else if (current) {
        gravAcc += dt;
        const gravity = dropMs(level);
        while (gravAcc >= gravity) {
          gravAcc -= gravity;
          if (!tryMove(0, 1, false)) break;
        }
      }
      if (current && !fits(shifted(current, 0, 1))) {
        if (!skipLock) {
          lockAcc += dt;
          if (lockAcc >= LOCK_MS) lockPiece();
        }
      } else if (status === "playing") {
        lockAcc = 0;
      }
      skipLock = false;
    }

    function ghostY() {
      if (!current) return null;
      let y = current.y;
      while (fits(shifted(current, 0, y + 1 - current.y))) y += 1;
      return y === current.y ? null : y;
    }

    function snapshot() {
      const into = lines % 10;
      return {
        status: status,
        score: score,
        lines: lines,
        level: level,
        dropMs: dropMs(level),
        linesInto: into,
        linesToNext: into === 0 ? 10 : 10 - into,
        board: board.map(function (row) { return row.slice(); }),
        current: current ? { id: current.id, rot: current.rot, x: current.x, y: current.y } : null,
        ghostY: ghostY(),
        queue: queue.slice(0, 3),
        holdId: holdId,
        holdLocked: holdLocked,
        clearingRows: clearingRows.slice(),
        banner: banner ? { title: banner.title, detail: banner.detail, life: banner.life } : null,
      };
    }

    reset();
    return { press: press, release: release, tick: tick, snapshot: snapshot };
  }

  // Five compact General MIDI sequences. Synthesized locally with Web Audio.
  // MIDI carries notes, not instrument samples. This is a lightweight synth approximation.
  const SONGS = [
    {name: 'Let’s Go!', midi: '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hj4AAJY8f4VQhjwAAJY7f4NghjsAAJY5f4VQhjkAAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZDf4VQhkMAAJZAf4NghkAAAJY+f4VQhj4AAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZAf4VQhkAAAJY7f4NghjsAAJY5f4VQhjkAAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZAf4VQhkAAAJY5f4NghjkAAJY3f4VQhjcAAJY+f4VQhj4AAJZAf4NghkAAAJY+f4VQhj4AAJY8f4VQhjwAAJY7f4NghjsAAJY5f4VQhjkAAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZDf4VQhkMAAJZAf4NghkAAAJY+f4VQhj4AAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZAf4VQhkAAAJY7f4NghjsAAJY5f4VQhjkAAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZAf4VQhkAAAJY5f4NghjkAAJY3f4VQhjcAAJY+f4VQhj4AAJZAf4NghkAAAJY+f4VQhj4AAJY8f4VQhjwAAJY7f4NghjsAAJY5f4VQhjkAAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZDf4VQhkMAAJZAf4NghkAAAJY+f4VQhj4AAJY8f4VQhjwAAJZAf4NghkAAAJY+f4VQhj4AAJZAf4VQhkAAAJY7f4NghjsAAP8vAA=='},
    {name: 'Battle Loop', midi: 'TVRoZAAAAAYAAQAJA8BNVHJrAAAAnQD/fzQFDxIDA39/AP8BBShTcGVha2VycyAoUmVhbHRlayBIaWdoIERlZmluaXRpb24gQXVkaW8pAP9/DwUPHDIwMTUuMDEuMTIBAwD/fywFDy1NaWNyb3NvZnQgU2FucyBTZXJpZiw4LjI1LEZhbHNlLEZhbHNlLDEsMAD/WAQEAhgIAP9RAwdTAAD/fwMFDwoA/y8AAP8vAAD/LwBNVHJrAAAB+gD/fwUFDwlISADAMQCwCmcA/38PBQ8GR2VuZXJhbCBNSURJAP8DB1RyYWNrIDEAkDl/ngCAOQAAkD5/ngCAPgAAkEB/ngCAQAAAkEN/ngCAQwAAkDl/AJBFf54AgEUAAIA5AACQPn8AkEd/ngCARwAAgD4AAJBIfwCQQH+eAIBAAACASAAAkEN/AJBKf54AgEoAAIBDAACQNH8AkDl/ngCAOQAAgDQAAJA0fwCQPn+eAIA+AACANAAAkDR/AJA9f54AgD0AAIA0AACQNH8AkDt/ngCAOwAAgDQAAJA0fwCQOX+eAIA5AACANAAAkDR/AJA+f54AgD4AAIA0AACQNH8AkD1/ngCAPQAAgDQAAJA0fwCQO3+eAIA7AACANAAAkC1/ngCALQAAkC9/ngCALwAAkDB/ngCAMAAAkDJ/ngCAMgAAkC1/AJBFfwD/fwMFDw6DYIBFAJoggC0AAJAvfwCQRX8A/38DBQ8Og2CARQCaIIAvAACQMH8AkEV/AP9/AwUPDoNggEUAmiCAMAAAkDJ/AJBFfwD/fwMFDw6DYIBFAJoggDIAAJA5f54AgDkAAJA7f54AgDsAAJA8f54AgDwAAJA+f54AgD4AAJBFf54AgEUAAJBHf54AgEcAAJBIf54AgEgAAJBKf54AgEoAAP8vAAD/LwAA/y8ATVRyawAADVcAwWsA/38FBQ8JCEAA/38PBQ8GR2VuZXJhbCBNSURJAP8DB1RyYWNrIDIAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/gXCBRwAAkUN/gXCBQwAAkUh/gXCBSAAAkUN/gXCBQwAAkUp/gXCBSgAAkUN/gXCBQwAAkUx/gXCBTAAAkUh/gXCBSAAAkUp/gXCBSgAAkUx/gXCBTAAAkU9/gXCBTwAAkTl/gXCBOQAAkUB/gXCBQAAAkUN/gXCBQwAAkUV/gXCBRQAAkUN/gXCBQwAAkUd/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cIkmAI0QmSZ/gXCJJgCNEJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZOX+BcIk5AIVQmSZ/gXCJJgCNEJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAgXCZJn+BcIkmAIVQmSZ/gXCJJgCFUJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIVQmSZ/gXCJJgCFUJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmTl/gXCJOQCUUJkmf4FwiSYAAJkmf4FwiSYAAJkmf3iJJgAAmSZ/eIkmAACZJn+BcIkmAACZOX+BcIk5AJRQmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/eIkmAACZJn94iSYAAJkmf4FwiSYAAJk5f4FwiTkAlFCZJn+BcIkmAACZJn+BcIkmAACZJn94iSYAAJkmf3iJJgAAmSZ/gXCJJgAAmTl/gXCJOQCUUJkmf4FwiSYAAJkmf4FwiSYAAJkmf3iJJgAAmSZ/eIkmAACZJn+BcIkmAACZOX+BcIk5AJRQmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/eIkmAACZJn94iSYAAJkmf4FwiSYAAJk5f4FwiTkAlFCZJn+BcIkmAACZJn+BcIkmAACZJn94iSYAAJkmf3iJJgAAmSZ/gXCJJgAAmTl/gXCJOQCUUJkmf4FwiSYAAJkmf4FwiSYAAJkmf3iJJgAAmSZ/eIkmAACZJn+BcIkmAACZOX+BcIk5AJRQmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/eIkmAACZJn94iSYAAJkmf4FwiSYAAJk5f4FwiTkAhVCZJn+BcIkmAI0QmSZ/gXCJJgCNEJkmf4FwiSYAjRCZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgCHQJkmf4FwiSYAjRCZJn+BcIkmAI0QmSZ/gXCJJgCNEJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZ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/38DBQ8OgXCFOQCBcJVAfwD/fwMFDw6BcIVAAIFwlUN/AP9/AwUPDoFwhUMAgXCVRX8A/38DBQ8OgXCFRQCBcJVDfwD/fwMFDw6BcIVDAIFwlUV/AP9/AwUPDoFwhUUAgXCVQ38A/38DBQ8OgXCFQwCBcJVAfwD/fwMFDw6BcIVAAIFwlTl/AP9/AwUPDoFwhTkAgXCVQH8A/38DBQ8OgXCFQACBcJVDfwD/fwMFDw6BcIVDAIFwlUJ/AP9/AwUPDoFwhUIAgXCVQ38A/38DBQ8OgXCFQwCBcJVCfwD/fwMFDw6BcIVCAIFwlUB/AP9/AwUPDoFwhUAAgXCVPn8A/38DBQ8OgXCFPgCBcJU5fwD/fwMFDw6BcIU5AIFwlUB/AP9/AwUPDoFwhUAAgXCVPn8A/38DBQ8OgXCFPgCBcJVAfwD/fwMFDw6BcIVAAIFwlUN/AP9/AwUPDoFwhUMAgXCVQn8A/38DBQ8OgXCFQgCBcJVDfwD/fwMFDw6BcIVDAIFwlUV/AP9/AwUPDoFwhUUAgXCVOX8A/38DBQ8OgXCFOQCBcJVIfwD/fwMFDw6BcIVIAIFwlUd/AP9/AwUPDoFwhUcAgXCVRX8A/38DBQ8OgXCFRQCBcJVDfwD/fwMFDw6BcIVDAIFwlUB/AP9/AwUPDoFwhUAAgXCVQ38A/38DBQ8OgXCFQwCBcJVFfwD/fwMFDw6BcIVFAIHxcJU5f4dAhTkAAJU+fwD/fwUFDw8ACIVQhT4AAJVDfwD/fwUFDw8ACIVQhUMAAJVFf4EghUUAAJVDf4EghUMAAJVAf4EghUAAAJU+f4NghT4AAJVAf4NghUAAAJU5f4dAhTkAAJU+fwD/fwUFDw8ACIVQhT4AAJVDfwD/fwUFDw8ACIVQhUMAAJVFf4EghUUAAJVDf4EghUMAAJVAf4EghUAAAJU+f4NghT4AAJVAf4NghUAAAJU5f4dAhTkAAJU+fwD/fwUFDw8ACIVQhT4AAJVDfwD/fwUFDw8ACIVQhUMAAJVFf4EghUUAAJVDf4EghUMAAJVAf4EghUAAAJU+f4NghT4AAJVAf4NghUAAAJU5f4dAhTkAAJU+fwD/fwUFDw8ACIVQhT4AAJVDfwD/fwUFDw8ACIVQhUMAAJVFf4EghUUAAJVDf4EghUMAAJVAf4EghUAAAJU+f4NghT4AAJVAf4NghUAA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'},
    {name: 'Borderline Space', midi: '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YIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAACSRX+DYIJFAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSRX+DYIJFAACSTH+DYIJMAACSSn+BcIJKAACSSH+BcIJIAACSR3+DYIJHAAD/LwBNVHJrAAABjwD/fwUFDwkAQAD/fw8FDwZHZW5lcmFsIE1JREkAswofALMHfwD/fyIFDyP/AAAAAQEAAAoAPAA7ADoAOQA4ADcANgA1ADQAMwAyAMNrAP8DB1RyYWNrIDUA/yABA4LoAJNAf3iTRX94k0h/nBCDSAAAg0UAAINAAACTQH94k0N/eJNHf5tUg0MAPINAAACTPn88k0N/PJNIf3iDRwCcEIM+AACTQH88g0MAPINIAACTRH94k0d/nBCDRwAAg0QAAINAAACTQH94k0V/eJNIf5wQg0gAAINFAACDQAAAk0B/eJNDf3iTR3+bVINDADyDQAAAkz5/PJNDfzyTSH94g0cAnBCDPgAAk0B/PINDADyDSAAAk0R/eJNHf5wQg0cAAINEAACDQAAAk0B/eJNFf3iTSH+cEINIAACDRQAAg0AAAJNAf3iTQ394k0d/m1SDQwA8g0AAAJM+fzyTQ388k0h/eINHAJwQgz4AAJNAfzyDQwA8g0gAAJNEf3iTR3+cEINHAACDRAAAg0AAAP8vAE1UcmsAAADJAP9/BQUPCQBAAP9/DwUPBkdlbmVyYWwgTUlESQC0B38AxHQA/wMHVHJhY2sgNgD/IAEEg+AAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAAlEB/jwCEQAAA/y8ATVRyawAABU0A/38FBQ8JAEAA/38PBQ8GR2VuZXJhbCBNSURJALUKKAC1By4AxQAA/wMHVHJhY2sgNAD/IAEFgfFwlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/g2CFSgAAlUx/g2CFTAAAlUV/g2CFRQAAlUx/g2CFTAAAlUp/gXCFSgAAlUh/gXCFSAAAlUd/g2CFRwAA/y8ATVRyawAAAWkA/38FBQ8JQEgA/38PBQ8GR2VuZXJhbCBNSURJALYHQwC2CmkAxmsA/wMHVHJhY2sgNQD/IAEGgulwlkB/eJZFf3iWSH+cEIZAAACGRQAAhkgAAJZAf3iWQ394lkd/m1SGQwA8hkAAAJY+fzyWQ388lkh/eIZHAJwQhj4AAJZAfzyGQwA8hkgAAJZEf3iWR3+cEIZAAACGRAAAhkcAAJZAf3iWRX94lkh/nBCGQAAAhkUAAIZIAACWQH94lkN/eJZHf5tUhkMAPIZAAACWPn88lkN/PJZIf3iGRwCcEIY+AACWQH88hkMAPIZIAACWRH94lkd/nBCGQAAAhkQAAIZHAACWQH94lkV/eJZIf5wQhkAAAIZFAACGSAAAlkB/eJZDf3iWR3+bVIZDADyGQAAAlj5/PJZDfzyWSH94hkcAnBCGPgAAlkB/PIZDADyGSAAAlkR/eJZHf5wQhkAAAIZEAACGRwAA/y8A'},
    {name: 'Final Push', midi: 'TVRoZAAAAAYAAQAGA8BNVHJrAAAAYwD/fwsFDxIDA39/AP8BBgD/fw8FDxwyMDEyLjA1LjEwAQMA/38qBQ8tTWljcm9zb2Z0IFNhbnMgU2VyaWYsOC4yNSxGYWxzZSxGYWxzZSwxAP9YBAQCGAgA/1EDA+VXAP8vAE1UcmsAAAM4ALAHaAD/fwUFDwlIQAD/fw8FDwZHZW5lcmFsIE1JREkA/38uBQ8jAQAAAAIBAAAKAEMAQgBBAEAAPwA+AD0APAA7ADoAOQALAAAAAAAEAAIAAADAMAD/AwdUcmFjayAxAJA7fwD/fwUFDw8ACACQL3+WQIA7AACQO3+HQIAvAACAOwAAkDl/AP9/BQUPDwAIAJAyf5ZAgDkAAJA5f4dAgDIAAIA5AACQPn8A/38FBQ8PAAgAkC1/lkCAPgAAkD5/h0CALQAAgD4AAJBAfwD/fwMFDw4AkDB/g2CAQACDYJBAfwD/fwMFDw6DYIBAAINgkEN/AP9/AwUPDoNggEMAg2CQQ38A/38DBQ8Og2CAQwCDYIAwAACQO38A/38FBQ8PAAgAkC9/lkCAOwAAkDt/h0CALwAAgDsAAJA5fwD/fwUFDw8ACACQMn+WQIA5AACQOX+HQIAyAACAOQAAkD5/AP9/BQUPDwAIAJAvf5ZAgD4AAJA+f4dAgC8AAIA+AACQQH8A/38DBQ8OAJA0f4NggEAAg2CQQH8A/38DBQ8Og2CAQACDYJBDfwD/fwMFDw6DYIBDAINgkEN/AP9/AwUPDoNggEMAg2CANAAAkDt/AP9/BQUPDwAIAJA3f5ZAgDsAAJA7f4dAgDcAAIA7AACQOX8A/38FBQ8PAAgAkDR/lkCAOQAAkDl/h0CANAAAgDkAAJA+fwD/fwUFDw8ACACQL3+WQIA+AACQPn+HQIAvAACAPgAAkEB/AP9/AwUPDgCQMn+DYIBAAINgkEB/AP9/AwUPDoNggEAAg2CQQ38A/38DBQ8Og2CAQwCDYJBDfwD/fwMFDw6DYIBDAINggDIAAJA7fwD/fwUFDw8ACACQL3+WQIA7AACQO3+HQIAvAACAOwAAkDl/AP9/BQUPDwAIAJAqf5ZAgDkAAJA5f4dAgCoAAIA5AACQPn8A/38FBQ8PAAgAkCt/lkCAPgAAkD5/h0CAKwAAgD4AAJBAfwD/fwMFDw4AkC1/g2CAQACDYJBAfwD/fwMFDw6DYIBAAINgkEN/AP9/AwUPDoNggEMAg2CQQ38A/38DBQ8Og2CAQwCDYIAtAAD/LwBNVHJrAAAIvQCxB2gAsQpqAP9/BQUPCQhAAP9/DwUPBkdlbmVyYWwgTUlESQDBBwD/AwdUcmFjayAyAJFTfwD/fwMFDw6BcIFTAIFwkUd/AP9/AwUPDoFwgUcAgXCRTH8A/38DBQ8OgXCBTACBcJFHfwD/fwMFDw6BcIFHAIFwkVF/AP9/AwUPDoFwgVEAgXCRR38A/38DBQ8OgXCBRwCBcJFOfwD/fwMFDw6BcIFOAIFwkUd/AP9/AwUPDoFwgUcAgXCRU38A/38DBQ8OgXCBUwCBcJFHfwD/fwMFDw6BcIFHAIFwkUx/AP9/AwUPDoFwgUwAgXCRR38A/38DBQ8OgXCBRwCBcJFRfwD/fwMFDw6BcIFRAIFwkUd/AP9/AwUPDoFwgUcAgXCRTn8A/38DBQ8OgXCBTgCBcJFHfwD/fwMFDw6BcIFHAIFwkVN/AP9/AwUPDoFwgVMAgXCRR38A/38DBQ8OgXCBRwCBcJFMfwD/fwMFDw6BcIFMAIFwkUd/AP9/AwUPDoFwgUcAgXCRUX8A/38DBQ8OgXCBUQCBcJFHfwD/fwMFDw6BcIFHAIFwkU5/AP9/AwUPDoFwgU4AgXCRR38A/38DBQ8OgXCBRwCBcJFTfwD/fwMFDw6BcIFTAIFwkUd/AP9/AwUPDoFwgUcAgXCRTH8A/38DBQ8OgXCBTACBcJFHfwD/fwMFDw6BcIFHAIFwkVF/AP9/AwUPDoFwgVEAgXCRR38A/38DBQ8OgXCBRwCBcJFOfwD/fwMFDw6BcIFOAIFwkUd/AP9/AwUPDoFwgUcAgXCRU38A/38DBQ8OgXCBUwCBcJFHfwD/fwMFDw6BcIFHAIFwkUx/AP9/AwUPDoFwgUwAgXCRR38A/38DBQ8OgXCBRwCBcJFRfwD/fwMFDw6BcIFRAIFwkUd/AP9/AwUPDoFwgUcAgXCRTn8A/38DBQ8OgXCBTgCBcJFHfwD/fwMFDw6BcIFHAIFwkVN/AP9/AwUPDoFwgVMAgXCRR38A/38DBQ8OgXCBRwCBcJFMfwD/fwMFDw6BcIFMAIFwkUd/AP9/AwUPDoFwgUcAgXCRUX8A/38DBQ8OgXCBUQCBcJFHfwD/fwMFDw6BcIFHAIFwkU5/AP9/AwUPDoFwgU4AgXCRR38A/38DBQ8OgXCBRwCBcJFTfwD/fwMFDw6BcIFTAIFwkUd/AP9/AwUPDoFwgUcAgXCRTH8A/38DBQ8OgXCBTACBcJFHfwD/fwMFDw6BcIFHAIFwkVF/AP9/AwUPDoFwgVEAgXCRR38A/38DBQ8OgXCBRwCBcJFOfwD/fwMFDw6BcIFOAIFwkUd/AP9/AwUPDoFwgUcAgXCRU38A/38DBQ8OgXCBUwCBcJFHfwD/fwMFDw6BcIFHAIFwkUx/AP9/AwUPDoFwgUwAgXCRR38A/38DBQ8OgXCBRwCBcJFRfwD/fwMFDw6BcIFRAIFwkUd/AP9/AwUPDoFwgUcAgXCRTn8A/38DBQ8OgXCBTgCBcJFHfwD/fwMFDw6BcIFHAIFwkVN/AP9/AwUPDoFwgVMAgXCRR38A/38DBQ8OgXCBRwCBcJFMfwD/fwMFDw6BcIFMAIFwkUd/AP9/AwUPDoFwgUcAgXCRUX8A/38DBQ8OgXCBUQCBcJFHfwD/fwMFDw6BcIFHAIFwkU5/AP9/AwUPDoFwgU4AgXCRR38A/38DBQ8OgXCBRwCBcJFTfwD/fwMFDw6BcIFTAIFwkUd/AP9/AwUPDoFwgUcAgXCRTH8A/38DBQ8OgXCBTACBcJFHfwD/fwMFDw6BcIFHAIFwkVF/AP9/AwUPDoFwgVEAgXCRR38A/38DBQ8OgXCBRwCBcJFOfwD/fwMFDw6BcIFOAIFwkUd/AP9/AwUPDoFwgUcAgXCRU38A/38DBQ8OgXCBUwCBcJFHfwD/fwMFDw6BcIFHAIFwkUx/AP9/AwUPDoFwgUwAgXCRR38A/38DBQ8OgXCBRwCBcJFRfwD/fwMFDw6BcIFRAIFwkUd/AP9/AwUPDoFwgUcAgXCRTn8A/38DBQ8OgXCBTgCBcJFHfwD/fwMFDw6BcIFHAIFwkVN/AP9/AwUPDoFwgVMAgXCRR38A/38DBQ8OgXCBRwCBcJFMfwD/fwMFDw6BcIFMAIFwkUd/AP9/AwUPDoFwgUcAgXCRUX8A/38DBQ8OgXCBUQCBcJFHfwD/fwMFDw6BcIFHAIFwkU5/AP9/AwUPDoFwgU4AgXCRR38A/38DBQ8OgXCBRwCBcJFTfwD/fwMFDw6BcIFTAIFwkUd/AP9/AwUPDoFwgUcAgXCRTH8A/38DBQ8OgXCBTACBcJFHfwD/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f4FwiSoAAIkmAIVQmSp/gXCJKgCFUJkmfwCZKn+BcIkqAACJJgCBcJkqfwCZLn+BcIkuAACJKgCFUJkqf4FwiSoAgXCZJn8AmSp/gXCJKgAAiSYAhVCZJn8AmSp/gXCJKgAAiSYAhVCZJn8AmSp/gXCJKgAAiSYAgXCZJn8AmS5/AJkqf4FwiSoAAIkuAACJJgCBcJk5f4FwiTkAAJkqf4FwiSoAg2CZJn8AmSp/gXCJKgAAiSYAhVCZKn+BcIkqAIVQmSZ/AJkqf4FwiSoAAIkmAIFwmSp/AJkuf4FwiS4AAIkqAIVQmSp/gXCJKgCBcJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCBcJkmfwCZLn8AmSp/gXCJKgAAiS4AAIkmAINgmSp/gXCJKgCDYJkmfwCZKn+BcIkqAACJJgCFUJkqf4FwiSoAhVCZJn8AmSp/gXCJKgAAiSYAgXCZKn8AmS5/gXCJLgAAiSoAhVCZKn+BcIkqAIFwmSZ/AJkqf4FwiSoAAIkmAIVQmSZ/AJkqf4FwiSoAAIkmAIVQmSZ/AJkqfwCZOX+BcIk5AACJKgAAiSYAgXCZJn8AmS5/AJkqf4FwiSoAAIkuAACJJgCBcJk5f4FwiTkAAJkqf4FwiSoAg2CZJn8AmSp/gXCJKgAAiSYAhVCZKn+BcIkqAIVQmSZ/AJkqf4FwiSoAAIkmAIFwmSp/AJkuf4FwiS4AAIkqAIVQmSp/gXCJKgCBcJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCBcJkmfwCZLn8AmSp/gXCJKgAAiS4AAIkmAINgmSp/gXCJKgCDYJkmfwCZKn+BcIkqAACJJgCFUJkqf4FwiSoAhVCZJn8AmSp/gXCJKgAAiSYAgXCZKn8AmS5/gXCJLgAAiSoAhVCZKn+BcIkqAIFwmSZ/AJkqf4FwiSoAAIkmAIVQmSZ/AJkqf4FwiSoAAIkmAIVQmSZ/AJkqf4FwiSoAAIkmAIFwmSZ/AJkufwCZKn+BcIkqAACJLgAAiSYAgXCZOX+BcIk5AACZKn+BcIkqAINgmSZ/AJkqf4FwiSoAAIkmAIVQmSp/gXCJKgCFUJkmfwCZKn+BcIkqAACJJgCBcJkqfwCZLn+BcIkuAACJKgCFUJkqf4FwiSoAgXCZJn8AmSp/gXCJKgAAiSYAhVCZJn8AmSp/gXCJKgAAiSYAhVCZJn8AmSp/gXCJKgAAiSYAgXCZJn8AmS5/AJkqf4FwiSoAAIkuAACJJgCDYJkqf4FwiSoAg2CZJn8AmSp/gXCJKgAAiSYAhVCZKn+BcIkqAIVQmSZ/AJkqf4FwiSoAAIkmAIFwmSp/AJkuf4FwiS4AAIkqAIVQmSp/gXCJKgCBcJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCFUJkmfwCZKn+BcIkqAACJJgCBcJkmfwCZLn8AmSp/gXCJKgAAiS4AAIkmAAD/LwBNVHJrAAAIvQCzB0kAswoXAMMHAP8DB1RyYWNrIDIA/38PBQ8GR2VuZXJhbCBNSURJAP9/BQUPCQhAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAIFwk1N/AP9/AwUPDoFwg1MAgXCTR38A/38DBQ8OgXCDRwCBcJNMfwD/fwMFDw6BcINMAIFwk0d/AP9/AwUPDoFwg0cAgXCTUX8A/38DBQ8OgXCDUQCBcJNHfwD/fwMFDw6BcINHAIFwk05/AP9/AwUPDoFwg04AgXCTR38A/38DBQ8OgXCDRwCBcJNTfwD/fwMFDw6BcINTAIFwk0d/AP9/AwUPDoFwg0cAgXCTTH8A/38DBQ8OgXCDTACBcJNHfwD/fwMFDw6BcINHAIFwk1F/AP9/AwUPDoFwg1EAgXCTR38A/38DBQ8OgXCDRwCBcJNOfwD/fwMFDw6BcINOAIFwk0d/AP9/AwUPDoFwg0cAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAIFwk1N/AP9/AwUPDoFwg1MAgXCTR38A/38DBQ8OgXCDRwCBcJNMfwD/fwMFDw6BcINMAIFwk0d/AP9/AwUPDoFwg0cAgXCTUX8A/38DBQ8OgXCDUQCBcJNHfwD/fwMFDw6BcINHAIFwk05/AP9/AwUPDoFwg04AgXCTR38A/38DBQ8OgXCDRwCBcJNTfwD/fwMFDw6BcINTAIFwk0d/AP9/AwUPDoFwg0cAgXCTTH8A/38DBQ8OgXCDTACBcJNHfwD/fwMFDw6BcINHAIFwk1F/AP9/AwUPDoFwg1EAgXCTR38A/38DBQ8OgXCDRwCBcJNOfwD/fwMFDw6BcINOAIFwk0d/AP9/AwUPDoFwg0cAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAIFwk1N/AP9/AwUPDoFwg1MAgXCTR38A/38DBQ8OgXCDRwCBcJNMfwD/fwMFDw6BcINMAIFwk0d/AP9/AwUPDoFwg0cAgXCTUX8A/38DBQ8OgXCDUQCBcJNHfwD/fwMFDw6BcINHAIFwk05/AP9/AwUPDoFwg04AgXCTR38A/38DBQ8OgXCDRwCBcJNTfwD/fwMFDw6BcINTAIFwk0d/AP9/AwUPDoFwg0cAgXCTTH8A/38DBQ8OgXCDTACBcJNHfwD/fwMFDw6BcINHAIFwk1F/AP9/AwUPDoFwg1EAgXCTR38A/38DBQ8OgXCDRwCBcJNOfwD/fwMFDw6BcINOAIFwk0d/AP9/AwUPDoFwg0cAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAIFwk1N/AP9/AwUPDoFwg1MAgXCTR38A/38DBQ8OgXCDRwCBcJNMfwD/fwMFDw6BcINMAIFwk0d/AP9/AwUPDoFwg0cAgXCTUX8A/38DBQ8OgXCDUQCBcJNHfwD/fwMFDw6BcINHAIFwk05/AP9/AwUPDoFwg04AgXCTR38A/38DBQ8OgXCDRwCBcJNTfwD/fwMFDw6BcINTAIFwk0d/AP9/AwUPDoFwg0cAgXCTTH8A/38DBQ8OgXCDTACBcJNHfwD/fwMFDw6BcINHAIFwk1F/AP9/AwUPDoFwg1EAgXCTR38A/38DBQ8OgXCDRwCBcJNOfwD/fwMFDw6BcINOAIFwk0d/AP9/AwUPDoFwg0cAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAIFwk1N/AP9/AwUPDoFwg1MAgXCTR38A/38DBQ8OgXCDRwCBcJNMfwD/fwMFDw6BcINMAIFwk0d/AP9/AwUPDoFwg0cAgXCTUX8A/38DBQ8OgXCDUQCBcJNHfwD/fwMFDw6BcINHAIFwk05/AP9/AwUPDoFwg04AgXCTR38A/38DBQ8OgXCDRwCBcJNTfwD/fwMFDw6BcINTAIFwk0d/AP9/AwUPDoFwg0cAgXCTTH8A/38DBQ8OgXCDTACBcJNHfwD/fwMFDw6BcINHAIFwk1F/AP9/AwUPDoFwg1EAgXCTR38A/38DBQ8OgXCDRwCBcJNOfwD/fwMFDw6BcINOAIFwk0d/AP9/AwUPDoFwg0cAgXCTU38A/38DBQ8OgXCDUwCBcJNHfwD/fwMFDw6BcINHAIFwk0x/AP9/AwUPDoFwg0wAgXCTR38A/38DBQ8OgXCDRwCBcJNRfwD/fwMFDw6BcINRAIFwk0d/AP9/AwUPDoFwg0cAgXCTTn8A/38DBQ8OgXCDTgCBcJNHfwD/fwMFDw6BcINHAAD/fwMFDwoA/y8A'},
    {name: 'Regular Battle', midi: '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PwLhcT8B4XA/AeFvPwHhbj8C4W0/AeFsPwHhaz8B4Wo/AuFpPwHhaD8B4Wc/AeFmPwLhZT8B4WQ/AeFjPwHhYj8C4WE/AeFgPwHhXz8B4V4/AuFdPwHhXD8B4Vs/AeFaPwLhWT8B4Vg/AeFXPwHhVj8C4VU/AeFUPwHhUz8B4VI/AuFRPwHhUD8B4U8/AuFOPwHhTT8B4Uw/AeFLPwLhSj8B4Uk/AeFIPwHhRz8C4UY/AeFFPwHhRD8B4UM/AuFCPwHhQT8B4UA/AeE/PwLhPj8B4T0/AeE8PwHhOz8C4To/AeE5PwHhOD8B4Tc/AuE2PwHhNT8B4TQ/AeEzPwLhMj8B4TE/AeEwPwHhLz8C4S4/AeEtPwHhLD8B4Ss/AuEqPwHhKT8B4Sg/AeEnPwLhJj8B4SU/AeEkPwHhIz8C4SI/AeEhPwHhID8B4R8/AuEePwHhHT8B4Rw/AuEbPwHhGj8B4Rk/AeEYPwLhFz8B4RY/AeEVPwHhFD8C4RM/AeESPwHhET8B4RA/AuEPPwHhDj8B4Q0/AeEMPwLhCz8B4Qo/AeEJPwHhCD8C4Qc/AeEGPwHhBT8B4QQ/AuEDPwHhAj8B4QE/AeEAPwLhfz4B4X4+AeF9PgHhfD4C4Xs+AeF6PgHheT4B4Xg+AuF3PgHhdj4B4XU+AeF0PgLhcz4B4XI+AeFxPgHhcD4C4W8+AeFuPgHhbT4B4Ww+AuFrPgHhaj4B4Wk+AuFoPgHhZz4B4WY+AeFlPgLhZD4B4WM+AeFiPgHhYT4C4WA+AeFfPgHhXj4B4V0+AuFcPgHhWz4B4Vo+AeFZPgLhWD4B4Vc+AeFWPgHhVT4C4VQ+AeFTPgHhUj4B4VE+AuFQPgHhTz4B4U4+AeFNPgLhTD4B4Us+AeFKPgHhST4C4Ug+AeFHPgHhRj4B4UU+AuFEPgHhQz4B4UI+AeFBPgLhQD4B4T8+AeE+PgHhPT4C4Tw+AeE7PgHhOj4B4Tk+AuE4PgHhNz4B4TY+AuE1PgHhND4B4TM+AeEyPgLhMT4B4TA+AeEvPgHhLj4C4S0+AeEsPgHhKz4B4So+AuEpPgHhKD4B4Sc+AeEmPgLhJT4B4SQ+AeEjPgHhIj4C4SE+AeEgPgHhHz4B4R4+AuEdPgHhHD4B4Rs+AeEaPgLhGT4B4Rg+AeEXPgHhFj4C4RU+AeEUPgHhEz4B4RI+AuERPgHhED4B4Q8+AeEOPgLhDT4B4Qw+AeELPgHhCj4C4Qk+AeEIPgHhBz4B4QY+AuEFPgHhBD4B4QM+AoFRAADhAEAA4QI+AJFPf4JAgU8AAJFMf4JAgUwAAJFRf4JAgVEAAOEAQACRT38C4QFAAeECQALhA0AB4QRAAeEFQAHhBkAC4QdAAeEIQAHhCUAB4QpAAuELQAHhDEAB4Q1AAeEOQALhD0AB4RBAAeERQAHhEkAC4RNAAeEUQAHhFUAB4RZAAuEXQAHhGEAB4RlAAeEaQALhG0AB4RxAAeEdQAHhHkAC4R9AAeEgQAHhIUAB4SJAAuEjQAHhJEAB4SVAAeEmQALhJ0AB4ShAAeEpQAHhKkAC4StAAeEsQAHhLUAB4S5AAuEvQAHhMEAB4TFAAuEyQAHhM0AB4TRAAeE1QALhNkAB4TdAAeE4QAHhOUAC4TpAAeE7QAHhPEAB4T1AAuE+QAHhP0AB4UBAAeFBQALhQkAB4UNAAeFEQAHhRUAC4UZAAeFHQAHhSEAB4UlAAuFKQAHhS0AB4UxAAeFNQALhTkAB4U9AAeFQQAHhUUAC4VJAAeFTQAHhVEAB4VVAAuFWQAHhV0AB4VhAAeFZQALhWkAB4VtAAeFcQAHhXUAC4V5AAeFfQAHhYEAB4WFAAuFiQAHhY0AB4WRAAuFlQAHhZkAB4WdAAeFoQALhaUAB4WpAAeFrQAHhbEAC4W1AAeFuQAHhb0AB4XBAAuFxQAHhckAB4XNAAeF0QALhdUAB4XZAAeF3QAHheEAC4XlAAeF6QAHhe0AB4XxAAuF9QAHhfkAB4X9AAeEAQQLhAUEB4QJBAeEDQQHhBEEC4QVBAeEGQQHhB0EB4QhBAuEJQQHhCkEB4QtBAeEMQQLhDUEB4Q5BAeEPQQHhEEEC4RFBAeESQQHhE0EB4RRBAuEVQQHhFkEB4RdBAuEYQQHhGUEB4RpBAeEbQQLhHEEB4R1BAeEeQQHhH0EC4SBBAeEhQQHhIkEB4SNBAuEkQQHhJUEB4SZBAeEnQQLhKEEB4SlBAeEqQQHhK0EC4SxBAeEtQQHhLkEB4S9BAuEwQQHhMUEB4TJBAeEzQQLhNEEB4TVBAeE2QQHhN0EC4ThBAeE5QQHhOkEB4TtBAuE8QQHhPUEB4T5BAeE/QQLhQEEB4UFBAeFCQQHhQ0EC4URBAeFFQQHhRkEB4UdBAuFIQQHhSUEB4UpBAuFLQQHhTEEB4U1BAeFOQQLhT0EB4VBBAeFRQQHhUkEC4VNBAeFUQQHhVUEB4VZBAuFXQQHhWEEB4VlBAeFaQQLhW0EB4VxBAeFdQQHhXkEC4V9BAeFgQQHhYUEB4WJBAuFjQQHhZEEB4WVBAeFmQQLhZ0EB4WhBAeFpQQHhakEC4WtBAeFsQQHhbUEB4W5BAuFvQQHhcEEB4XFBAeFyQQLhc0EB4XRBAeF1QQHhdkEC4XdBAeF4QQHheUEB4XpBAuF7QQHhfEEB4X1BAoFPAADhAEAA4X5BAJFMf4JAgUwAAJFRf4JAgVEAAJFPf4JAgU8AAJFMf4JAgUwAAJFRfwD/fwMFDw6BcIFRAIFwkVF/AP9/AwUPDoFwgVEAiTCRRX8A/38DBQ8OgXCBRQCBcJFFfwD/fwMFDw6BcIFFAIkw/38DBQ8KAP8vAE1UcmsAAAikAP9/GgUPIwEAAAACAQEAAAAmAAEAAAAAAAQABAAAAP9/BQUPCQhAAP9/DwUPBkdlbmVyYWwgTUlESQD/AwdUcmFjayAzAMkAAP9/BAUPAwEAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAIVQmSZ/gXCJJgCFUJkmf4FwiSYAgXCZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCFUJkmf4FwiSYAhVCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIVQmSZ/gXCJJgCFUJkmf4FwiSYAgXCZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCFUJkmf4FwiSYAhVCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAJkmf4FwiSYAgXCZJn+BcIkmAACZJn+BcIkmAACZJn+BcIkmAIFwmSZ/gXCJJgAAmSZ/gXCJJgAAmSZ/gXCJJgCBcJkmf4FwiSYAAJkmf4FwiSYAAP8vAE1UcmsAABNfALIHawDCagD/fwUFDwkIQAD/fw8FDwZHZW5lcmFsIE1JREkA/wMHVHJhY2sgNACSRX+LIIJFAACSSH+LIIJIAACSTH+DYIJMAACSSn+DYIJKAACSSH+DYIJIAACSR3+DYIJHAACSSH+DYIJIAACSSn+DYIJKAACSTH+DYIJMAACSSn+DYIJKAACSTH+DYIJMAACSTX+DYIJNAACSTX+CQIJNAACSTH+CQIJMAACSSn+CQIJKAADiAEAAkkx/AuIBQAHiAkAC4gNAAeIEQAHiBUAB4gZAAuIHQAHiCEAB4glAAeIKQALiC0AB4gxAAeINQAHiDkAC4g9AAeIQQAHiEUAB4hJAAuITQAHiFEAB4hVAAeIWQALiF0AB4hhAAeIZQAHiGkAC4htAAeIcQAHiHUAB4h5AAuIfQAHiIEAB4iFAAeIiQALiI0AB4iRAAeIlQAHiJkAC4idAAeIoQAHiKUAB4ipAAuIrQAHiLEAB4i1AAeIuQALiL0AB4jBAAeIxQALiMkAB4jNAAeI0QAHiNUAC4jZAAeI3QAHiOEAB4jlAAuI6QAHiO0AB4jxAAeI9QALiPkAB4j9AAeJAQAHiQUAC4kJAAeJDQAHiREAB4kVAAuJGQAHiR0AB4khAAeJJQALiSkAB4ktAAeJMQAHiTUAC4k5AAeJPQAHiUEAB4lFAAuJSQAHiU0AB4lRAAeJVQALiVkAB4ldAAeJYQAHiWUAC4lpAAeJbQAHiXEAB4l1AAuJeQAHiX0AB4mBAAeJhQALiYkAB4mNAAeJkQALiZUAB4mZAAeJnQAHiaEAC4mlAAeJqQAHia0AB4mxAAuJtQAHibkAB4m9AAeJwQALicUAB4nJAAeJzQAHidEAC4nVAAeJ2QAHid0AB4nhAAuJ5QAHiekAB4ntAAeJ8QALifUAB4n5AAeJ/QAHiAEEC4gFBAeICQQHiA0EB4gRBAuIFQQHiBkEB4gdBAeIIQQLiCUEB4gpBAeILQQHiDEEC4g1BAeIOQQHiD0EB4hBBAuIRQQHiEkEB4hNBAeIUQQLiFUEB4hZBAeIXQQLiGEEB4hlBAeIaQQHiG0EC4hxBAeIdQQHiHkEB4h9BAuIgQQHiIUEB4iJBAeIjQQLiJEEB4iVBAeImQQHiJ0EC4ihBAeIpQQHiKkEB4itBAuIsQQHiLUEB4i5BAeIvQQLiMEEB4jFBAeIyQQHiM0EC4jRBAeI1QQHiNkEB4jdBAuI4QQHiOUEB4jpBAeI7QQLiPEEB4j1BAeI+QQHiP0EC4kBBAeJBQQHiQkEB4kNBAuJEQQHiRUEB4kZBAeJHQQLiSEEB4klBAeJKQQLiS0EB4kxBAeJNQQHiTkEC4k9BAeJQQQHiUUEB4lJB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AACSUX+CQIJRAACSRX+CQIJFAACST3+CQIJPAACSUX+CQIJRAACSRX+CQIJFAACST3+CQIJPAACSUX+CQIJRAACSRX+CQIJFAACST3+CQIJPAACSUX+CQIJRAACSRX+CQIJFAACSTn+CQIJOAACSUX+CQIJRAACSRX+CQIJFAACSTn+CQIJOAACSUX+CQIJRAACSRX+CQIJFAACSTn+CQIJOAACSUX+CQIJRAACSRX+CQIJFAACSTn+CQIJOAACSUX+CQIJRAACSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiSRX8A/38DBQ8OeIJFAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiST38A/38DBQ8OeIJPAHiSUX8A/38DBQ8OeIJRAHiSRX8A/38DBQ8OeIJFAHiSRX8A/38DBQ8OeIJFAHiSTH8A/38DBQ8OeIJMAHiST38A/38DBQ8O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gkCDUQAAk0V/gkCDRQAAk09/gkCDTwAAk1F/gkCDUQAAk0V/gkCDRQAAk09/gkCDTwAAk1F/gkCDUQAAk0V/gkCDRQAAk05/gkCDTgAAk1F/gkCDUQAAk0V/gkCDRQAAk05/gkCDTgAAk1F/gkCDUQAAk0V/gkCDRQAAk05/gkCDTgAAk1F/gkCDUQAAk0V/gkCDRQAAk05/gkCDTgAAk1F/gkCDUQAAk0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k0V/AP9/AwUPDniDRQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4k0V/AP9/AwUPDniDRQB4k0x/AP9/AwUPDniDTAB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k09/AP9/AwUPDniDTwB4k1F/AP9/AwUPDniDUQB4k0V/AP9/AwUPDniDRQB4/38DBQ8KAP8vAA=='},
  ];

  function decodeMidi(b64) {
    const str = atob(b64), data = Uint8Array.from(str, c => c.charCodeAt(0));
    const dv = new DataView(data.buffer); let p = 0;
    const u16 = () => { const v = dv.getUint16(p); p += 2; return v; };
    const u32 = () => { const v = dv.getUint32(p); p += 4; return v; };
    const ascii = n => { const s = str.slice(p,p+n); p += n; return s; };
    const vlq = () => { let v=0,b; do { b=data[p++]; v=(v<<7)|(b&127); } while(b&128 && p<data.length); return v; };
    if (ascii(4)!=='MThd') throw Error('Invalid MIDI');
    const header=u32(), format=u16(), count=u16(), division=u16(); p=8+header;
    if (division & 0x8000) throw Error('SMPTE MIDI unsupported');
    const events=[];
    for(let tr=0;tr<count;tr++) {
      if (ascii(4)!=='MTrk') break;
      const length=u32(), end=p+length; let tick=0, running=0;
      while(p<end) {
        tick+=vlq(); let status=data[p];
        if(status&0x80) {p++; running=status;} else status=running;
        if(status===0xff){const meta=data[p++],n=vlq();if(meta===0x51&&n===3){events.push({tick,kind:'tempo',value:(data[p]<<16)|(data[p+1]<<8)|data[p+2]});}p+=n;continue;}
        if(status===0xf0||status===0xf7){p+=vlq();continue;}
        const kind=status&0xf0,ch=status&15;
        const a=data[p++];const b=(kind===0xc0||kind===0xd0)?0:data[p++];
        if(kind===0x90&&b>0) events.push({tick,kind:'on',ch,note:a,velocity:b});
        else if(kind===0x80||(kind===0x90&&b===0)) events.push({tick,kind:'off',ch,note:a});
        else if(kind===0xc0) events.push({tick,kind:'program',ch,value:a});
      }
      p=end;
    }
    const order={tempo:0,program:1,off:2,on:3};
    events.sort((a,b)=>a.tick-b.tick||order[a.kind]-order[b.kind]);
    let last=0,seconds=0,tempo=500000;
    for(const e of events){seconds+=(e.tick-last)*tempo/1000000/division;last=e.tick;e.time=seconds;if(e.kind==='tempo')tempo=e.value;}
    return {events:events.filter(e=>e.kind!=='tempo'),duration:Math.max(seconds+0.4,1)};
  }

  function createMusic() {
    let ctx=null, master=null, analyser=null, wave=null, timer=null;
    let muted=false, volume=.30, index=0, song=null, cursor=0, origin=0;
    const active=new Map(), programs=new Uint8Array(16);
    let failed=false;
    const noiseCache={};
    function label(){if(failed)return 'error';if(muted)return 'muted';if(!ctx)return 'off';return ctx.state==='running'?'playing':ctx.state;}
    function level(){if(!analyser||!wave||muted)return 0;analyser.getByteTimeDomainData(wave);let s=0;for(const v of wave){let a=(v-128)/128;s+=a*a;}return Math.sqrt(s/wave.length);}
    function tone(ch,note,velocity,when){
      if(!ctx||muted&&volume===0)return;
      if(ch===9){ // short synthetic percussion
        const osc=ctx.createOscillator(), g=ctx.createGain();osc.type=note>=42?'triangle':'square';
        osc.frequency.setValueAtTime(note>=42?400:note<40?95:180,when);
        osc.frequency.exponentialRampToValueAtTime(note>=42?170:45,when+.11);
        g.gain.setValueAtTime(.0001,when);g.gain.exponentialRampToValueAtTime(Math.max(.003,velocity/127*.13),when+.004);
        g.gain.exponentialRampToValueAtTime(.0001,when+.13);
        osc.connect(g).connect(master);osc.start(when);osc.stop(when+.15);return;
      }
      const program=programs[ch],freq=440*Math.pow(2,(note-69)/12);
      const osc=ctx.createOscillator(),amp=ctx.createGain(),filter=ctx.createBiquadFilter();
      osc.type=program>=80?'sawtooth':program>=32&&program<40?'triangle':program>=48&&program<56?'sawtooth':program>=0&&program<8?'triangle':'square';
      osc.frequency.setValueAtTime(freq,when);
      filter.type='lowpass';filter.frequency.value=program>=80?3000:program>=32&&program<40?1000:2200;
      const v=velocity/127*.13;
      amp.gain.setValueAtTime(.0001,when);amp.gain.linearRampToValueAtTime(v,when+.016);
      amp.gain.setTargetAtTime(v*.6,when+.04,.13);
      osc.connect(filter).connect(amp).connect(master);osc.start(when);
      const key=ch+':'+note;
      const voices=active.get(key)||[];voices.push({osc,amp});active.set(key,voices);
      if(voices.length>3) release(voices.shift(),when);
    }
    function release(voice,when){try{voice.amp.gain.cancelScheduledValues(when);voice.amp.gain.setTargetAtTime(.0001,when,.045);voice.osc.stop(when+.3);}catch(e){}}
    function allOff(){for(const voices of active.values())for(const v of voices)release(v,ctx.currentTime);active.clear();}
    function choose(n){index=n;song=decodeMidi(SONGS[index].midi);cursor=0;programs.fill(0);if(ctx){allOff();origin=ctx.currentTime+.06;}}
    function schedule(){if(!ctx||ctx.state!=='running'||!song)return;
      let now=ctx.currentTime;
      if(now-origin>=song.duration){choose(index);origin=ctx.currentTime+.06;now=ctx.currentTime;}
      const horizon=now+.16;
      while(cursor<song.events.length&&origin+song.events[cursor].time<horizon){
        const e=song.events[cursor++],t=Math.max(now+.004,origin+e.time);
        if(e.kind==='program')programs[e.ch]=e.value;
        if(e.kind==='on')tone(e.ch,e.note,e.velocity,t);
        if(e.kind==='off'){const key=e.ch+':'+e.note,voices=active.get(key);if(voices&&voices.length){release(voices.shift(),t);if(!voices.length)active.delete(key);}}
      }
    }
    function unlock(){if(!ctx){try{
      const AC=globalThis.AudioContext||globalThis.webkitAudioContext;ctx=new AC();master=ctx.createGain();master.gain.value=muted?0:volume;analyser=ctx.createAnalyser();analyser.fftSize=256;wave=new Uint8Array(256);master.connect(analyser);analyser.connect(ctx.destination);
      choose(index);timer=setInterval(schedule,65);
    }catch(e){failed=true;return;}}if(ctx.state==='suspended')ctx.resume();}
    function toggle(){muted=!muted;if(ctx)master.gain.setTargetAtTime(muted?0:volume,ctx.currentTime,.02);return muted;}
    function setVolume(n){volume=Math.max(0,Math.min(1,Number(n)));if(ctx)master.gain.setTargetAtTime(muted?0:volume,ctx.currentTime,.02);}
    function random(){let n=index;if(SONGS.length>1)while(n===index)n=Math.floor(Math.random()*SONGS.length);choose(n);unlock();return SONGS[index].name;}
    function stop(){if(timer)clearInterval(timer);if(ctx){allOff();ctx.close();ctx=null;}}
    choose(0);
    return {unlock,toggle,setVolume,random,stop,label,level,songName:()=>SONGS[index].name};
  }

  let fxSeed = 2463534242;
  function fxRand() {
    fxSeed = (fxSeed * 1664525 + 1013904223) >>> 0;
    return fxSeed / 4294967296;
  }

  const mounts = new WeakMap();

  function mount(el) {
    const previous = mounts.get(el);
    if (previous) previous.destroy();

    let preset = null;
    if (Array.isArray(globalThis.__NEON_FORCE_PIECES) && globalThis.__NEON_FORCE_PIECES.length) {
      preset = globalThis.__NEON_FORCE_PIECES.slice();
    }
    const session = createSession(preset ? { pieces: preset } : undefined);
    const music = createMusic();
    const ac = new AbortController();
    let dead = false;
    let raf = 0;
    let lastNow = globalThis.performance ? performance.now() : Date.now();
    let clock = 0;
    let miniSig = "";
    let seenScore = 0;
    let scorePop = 0;
    let sparkMark = "";
    let flash = 0;
    let shock = null;
    const shards = [];


    const EMBEDDED_BACKGROUND = "data:image/webp;base64,UklGRoKTAABXRUJQVlA4WAoAAAAgAAAAnwUAKQMASUNDUMgBAAAAAAHIAAAAAAQwAABtbnRyUkdCIFhZWiAH4AABAAEAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAACRyWFlaAAABFAAAABRnWFlaAAABKAAAABRiWFlaAAABPAAAABR3dHB0AAABUAAAABRyVFJDAAABZAAAAChnVFJDAAABZAAAAChiVFJDAAABZAAAAChjcHJ0AAABjAAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAAgAAAAcAHMAUgBHAEJYWVogAAAAAAAAb6IAADj1AAADkFhZWiAAAAAAAABimQAAt4UAABjaWFlaIAAAAAAAACSgAAAPhAAAts9YWVogAAAAAAAA9tYAAQAAAADTLXBhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABtbHVjAAAAAAAAAAEAAAAMZW5VUwAAACAAAAAcAEcAbwBvAGcAbABlACAASQBuAGMALgAgADIAMAAxADZWUDgglJEAABAZBJ0BKqAFKgM/EYS4VSw/v7YoMspT8CIJSUVsc//7jPJtZzPD2mhMcIeH6c5R2Iv0f9bgP9R5XnT/8z4p/5XkJ+u9Mzi5fleoH5D/+PzZ553ob/pfPpa7NLeTmaz/Hre4z+x5+fXHvv/j+fvhVy1Qevdv+f94e1j1g/3H/3esj6D/V3/cfS75tfm+7+70WfpZZGX8Q/9Pog+U/6/jL7+f6X9l7iv/Psf+u/9vPj+8f5zNT/2ecf2QlZ8qXSv/r4b/QQ/89bP6Xo11pz/99bv38TqaznZk7Li/QetGOofTmziD/aCgYUlyJG8nEcSZegm7r9mTsVcl1y/6iF4ATjIi2ZGq+1QoIgJoPWHSU8R6vn9TQ26Fg5qBNs2R78MoYC6eTMVzCYTm1ZUYg/2f7P9n+z/Z/t4wmSkIF+OAbiZFfl+PR8cFacAVHnxmivdyZ8SPK613CyIUT72jVLAI/o/ZI8kw0gh97UcyaEeabAns72EW5VVVVU58bGbT+T3Y1NH+Qe2Q91zQ5lJxC5yGNxgsQ7aFausul5SvjGsN7YqancqiHd+MEpy3HceT1d+1qIdGhaoxaLtmyO5HcjuR3I7qbmr9Rsd2mslof4ibp07r0GjDnogybfe8txYkyDmurI2o0PcTYAenB37V7Z+C14vYHtsoabFC0JhkzFiVlUQ+m7HcjuR3I7qaSMXRh9z+fufvB7Vka7DRWEMRTwwVtYXC5WiQKrHMclvnknMxCCgYVJFB3m0fRQd9/y6QX8vN2O5HcjuR3I7kdyvNRIQK/zPBG9RQIV5hEYBFz7kcvxZGRmiPKqmnEP3TGglOwB3gauaSrhy52dPx4Shxfg7Ogl1oBsvd3s/2goGFScrn9dNpDmBDU5TZSDeqkWriYg/2f7P/f5uHq2OYozEHdu/gu3YF00g4fb8R1AvqNomjxW5H2/Wq5z2WUueaukTFS6B3ardkrw96l2m7Jz3J5UGhtm7AVH8s+eZ1hS0YE8TdGYWW1sddyO5HcjuR97pDksAy0VLzmWZgjs9F+YKloC30lJsURLTr96pkWX6E1PTTFCVRYSzXXV5As+5NqexLdpvorBVZiIWWvAMENFnGBmHFvXcrF2YJB+7/C8OTCc2aV3s/2f7P+vYO3t910wJ8EvBbmdRUrZw8gS7A/o3ghMg3oZ7OE1iLkGEA+vy65aC6mj+Za9CtqKnH2xaupT6jeo+AXH5LVZ9pvFUz0q6xsvjnZYH/u3z0IaknM3ZWONbu37fcIBtqS1tIc9OylCzCSAX1LvZ/s/2f7P9ml+Nh/6h89LUWD8IXBxxeTz+5awTY03tC/zjc/9GZstV3hwjbemY0qoqu0r94+ZuJ6FqIMTfm/ScZxOIJ5brg8dsZckP7lTORFG82fJ+X93EwWwjmzw0b4g8SQw03EfJz6mVxnzoFfqX/XcjuScRqvRfW6au2M+dUwtAi9POXPlDjDdObWMU5sHKXaZIDJ6Cc8vyybRO3HuW5tT83bh4Nd+rOHb9UShR3oNKgfMUVQs1kt/QNvjpYYAcuf/NfFormPBv+NLshX3b8xTbP/6jruSc7HciyjPcUTtJebjB+kuEgePudmRry776IesdpuWgq6ed0ZSG1aUiyeypPM4hhEhYhDMnGFZb9d1VxUge51hvjp1A25jtRXfPL0AjguWgMMTSNA9+V7QbA5JzMQf9hRQ/zXUUNqyUNkGcc2dXTzC9CzuNnDm1iieAq9ufZ7QIdsZVSAGG1WZ92hkLZqQ82J9Hk56o7HtFmR3Xka4a6oVkqZWMzCgy4GQkcFL5+6D48W0//xgF2SluypHLFB44XYbvNDPbtuurpa4Ei5VJdV8P67nZux3JnzGVOE5ZKrMIefGV/eTwc44lIQ+rFfvGMRZF8ppkn433RGdFAba7AX/0+jFVU5Kc/87U3Ww7yvXjVH74uO2+rkraGKzOrbG8WWX5XAzMH6GlK5MG9Oe6ml7qXsB/o67slKRhZZNUE11jG49bXdqgwbZuUg5ePrKyfpubW1GkV6IX8RV2iUoT+CCUaFx3JjchIArXoTl8DKUSg0eIoaRM4+v69JgRlugHte6vOTP5CGrHzm4raFhdihyCILEWcUFrJqn4l6Kfgm37HBSDxtciY3xEtiH0yQOneI+pVTQOH3cE4gU7cE6zxB2h+uyXb0nsSvzlMSAq9oRzHzrClZRHla6uaa1EkSkFqrX3BSDVKNMs3Iydx2jw0meE1qxcKLypJqMJqJvP95d9AuZukJIbI679KPFTB+daoMGctx5D69qWuV4DVyHFVKdwP0dHbQjm9LEht0zyt0VTLHXvdWYXvurF75wXDq1YRmynJoS196XtYRzxk3aDpmt7WSxpfL6GIXo555vhpt/F//xEF/yW1bvWwmI2h2tOhWyONCTks/AZp9peOywExvniFneHeVWP82adRnUq/pX1NO/7VdU0XYY1S9Qp72MMTHul8SN//I5sIxMglxYX6sD/RGKlPBwrudIXXVHfQglk49ghPNLqjDhTy+Mzd8I5DeSCQuJlCL8yBR/EEu4WQ3G5TGiztN9gMqzzQnDZweWFOcNe/CXwZm9tpQxxaZ7uW3ov78x/tdfxQbBNXPd8ySROF7wBYByK8bokakGojjJv4M9ttIq/UeuTnxuJu1liXuay7rDuzNmDj05Fb6pzsF+HXcRgMNtOCAARYrW0VOOOn0dJ3KS0lrO+rtXzOHATLF+edX01tjdFV/bdXSA5Jynlhm7RaAOA7GG1fgy1OKLKEjM6QM9izNStDzghU7rEMp43/1AR9RTQV2YUsJ+dWLcjVcBQMwgnboQCefS32aDbU8QfZnf0msXdvYOwMviCDEqHdo1N42purqrieuOMV5KiWMJQ9t3x/9RyPwLoF3f6RsNYR4ON9OqJMTV5QB92hlihc/wB+ynE9pZ45jELj0OFJ+qh56gT/L+yGCyR9Z+X1RWQp3EKChF3TBtXvaDDdb35y4rLeM/+2lgaG0JHV9H7X/H849C9XDd+9/YZ60uJbTd8jrjHjcPiYSf7m+0FCTEY3j27gjkvq+a6vFsEpvCm2Ohc/jycPZsqPoArleTvUgkpD/rnfuGbMryvfNXSofdXtVj1AbPwv5h7VWjcHWu+JaXwf+yOdKMOU391zRt88dj5IOsrMw7ht/lLVy5KXsb9bQxTXXuZpOfGRdPCGLOa85PjZWyX1g78rudslbyLJCB5a3f0NgQNNBkzUaJS3NI9YZtG4QtWMYAUzQp2uNH95zLcNjMJjphj/gALLusDJYXKwMXS3aoljYVpf821tMn7ZC1Zi8MLtjVDuzaHkoryCNg0ygq6/tTNQpHo12uCAFle79IsifJ/tb480SGQElpZRGMwPznBC24HMAa9HypnxsMs/xMZLlxF2Tck9xJhiYrUgO/0ExjdU2fzuag6sJuKUIOGaogZ76wG/qvjF0j+Z3BFaiNu3szT3TmUyepMeFPe+j8Ol4909Q5C/NKcD+KiO6aaiqXeUbfQQnAJcJrx5Iwdp85sKKqLoklmieBwdcpWiGI/2uJKCO/FnxqV55OaFXpU5Tu5DjUD9FoAGwzv1+IjKJqSr6Bqar3bKci6tI4lZW1AS1hKtFlUu1Z467leShak9eoSdSHoKEPyV82eM/obEKrzwKvHd8VWCkObEmRHQP1UIPK0utqVbyt96eHVQXGcfaJHVZ8xbmjdx7um5hcibhr/5bzhoqqGNY/UoMc5SS2Od4OxloLQUNXv9BDtgS7CB/ovWrb7m03UsUFWT9IehzubxkKKf5RbOAaJYZYI69u9EiLJwop1pLDAN0m9I1kR4dFFS39iaILCw2niAImfZ4TT6ROn/PjwJM6oDLNW110JIvDivKE9hVOAdsNNsFgYY6AB59Kahp4tIzrwbJjOOV58L/yYDSLuZybGu5OdDOAEHvT39NG+4L/oHTTX1a5lG3sWnZ6lpfWtOmEK4mLAfnF2G16+L6y04aYY8nKVRUbjHB7KUs2toCFvf0UMF8kuw89WqdiUVaMP8PGRX+viYFtFCN73YVihWX1zVGb/gvDL6fXLPjJiMyfQBEphTrSPYN1vhVtqe4lZYhuPKFi2DH3jQDC1+uUs+m8cffIJ4ufh/vwf2YyHL/1zqOOrSvrW10sWBd1BktxE1q+hkZ7dp62NBhKX/KqhKP+bO6mDnb/I26k4WM/EthXH3pSf83m0bs0hcGqnS1TNMgTcZpzq79pVs8akLcE328Ln2TjONtuqgbGFVyFLi7gR649U+MRV0LjPYVJQ33ChLS9VJpYhi7Zj3SIOJrd9UIwS9blrrrLWNtbpVRU0ADnMdxQlQdam1hECSieZ8f2iF/IGzUm6buL0tg1pqd0oj2gGB0CkHLv2cv7X60peG79QqMLR6Wl//UvJ4zcHFBWbdR3/kwTZLNyrKgWK+veaFcPo2QFbfAHB65gXTWB+RzQFsWDj/5MJVja6HI4xUHkDOy+MoREo0kxyo7D+nsL8QSLYwUSLHdT7FlbnK8Prr0oJzoxnUiLdfN1FK7lyyJEOmonjs4qOVlxCrjxVniCCWQxBu8imf39FFjPGeLXUpnC5zHo4mYigAGAMkf5ixd3sULHqmS32hb1NbORN+t1I3tuNoIcZtXkmsw4H2+dFYxNG3u7kxqlpZszsmlJOMam26stHrxmJyhtuoGXSylUHrP8YOsgmI7LCpyvDDf1mQtdpupOOI+xpvsjPf2CvH/v02COi5TZ6XJwuprLxMWiUdeFYxRt1Ja5eqKNQozDlFqu8c5LHOQF2Wox+Yiz/Tt/ujZJehOnmG1MaKIrWirsqrCMkXu5g90p//VQp0yhC1wz6FQjIxBpwLAZpOdDA9rJCgVqMLDwtcY/bzCdvXThGp4DMC/2WkR3jecK4aNyUc8LsbrzeWKLdn6k/oSBKtx/MqF/ArqRtf6bKmd2c8vyDzO/BM9uSHytPWyneuTAEDvHif9YoTDWlp0L8CHRFuurGPNQluwxSoKzZp5W3CkcslK8cInk4VpQQD/gATuiTXyI0XDE6Uoh6ZantUzrGutqGHH1yPHaNNTbtP43A0mtJ8xBbJeUyv7UIDd6yrXOOSlHiZwORVUqljKvHMGGweJ6RX/Jp3w/EsQPLMWm/v1f/yuDh85sL83jfa2rnmgJOKKd21qXpwAvVkovlbqaHLY+QzuOv5t0PcFaOTwmATfOwX8pQPxpsAXb3UnccC6XyjieujkfQ03Vl/LKcF51QkWiTzX6K5Ff2K5L/9YLlCehzsFmwTuGKSXP2NdCIebiH+mwdttmS57mtA3AnG6UvxGEZq+n9EZZkrrZ27KwjPIHeuXWvZlu+n/ZbMb5HydigbS9SABOtMJ8DlrVNNzpSpCDL9vvZmGd1I/TgJDWr7c20M7xyfYb2Ts0du/eluF/b9oRryrOTIDxvHOCDdMKO2HcAfoszLjUN4XPra9JJE9GkXUiX2O7d6XvaO9Sa4W+8rbKeUhdzs4pgaL0aCjgqywG3hUTy4hbBH2WjCh/OtUi7+/hAtPbrTQXRm1V4/ySxpZp6II4IofcCiWd6dCZY5LfNe83pmhEjJY8Q7zsDv1RQU2hUJ8HMEZRf20CdVAB7q7ZbyErrnqqOkPPpKQUz0Mhca23k04dMcH42b1TI5C0fqKY3WpccayyoXz5rDZCcMHl30FUJgPdyuTbCT9Ktg472TjbZ+q/KuUqpVCcgdbalBT1zoOGyJNiHye2F8r8Jw5LUpBeXaLhJ6Ry3z7k+w78iEKsAGt8crP3OC7gvUqvT+DHFdrKF3vUz/3O3zU2+4Li5FT4eYY7TDd0sFwuEuG4hNr2VbVg83oUN95Q3eNuQLioMdwWtfcB3cu4SwEeSWNN0c+XKxFSDBFndCVskTtlgWtndqvHlvIbX2ROnPA7TUIs6A70/ucRobS15mFKle4E/h8UXhJb5temLGVornJdyR3VNLLHRdPp80ywW17dF2+KCeRLPmcg5D98Xao4rmrroqzF7fsUPZIgJW//7PZre943QF4sS2CqbGZTzWB7lgaVdRJTyyg2t1ZLcSaF3y5uS5Fbs/LQPlQzXyGc/5npcdG3o5tQryXOLyGAd6sdWpCfJwPCWz1bIESPYCH0CXGj3VWAlP9WW8swiJfMUmHMY5WolnNjKYJsQDJYAwGndXJdwBdEiK3Ce5XHZ4hmXlsC6GJhLXH1CCSgwpDcOKixSifSNH7UHsev8qmzcQ2Q/TK3V4HmtueBF8MjRchn3NS2LUfWxmzQrt5KPTjLtmO1ZGpcbktFsNkgarxGxl+WhT6XAD37sOn5aEQy+GVIuzqQdR+N/EnZa3nW/AMaFszuBZsXoEh6QZkY+g3ympc5W7nEzq87ba5uMUws66QHeDwmWcBvPHPTLLUHgmTJm5pgj2gmneNtkxGDCHbbzFRqvx/cRrUrHjT6Bv+mdkvAhGfUCZeRNyCWvQmjkxdGrbapKRqppXI4WtboNGPQSwxrl0gn4FAvJrV8CtM7VEjyj8o0RkzkdD3+mJteUY7ZQVa7k+O66BqYSusXj2UARxuaPaZQutVj/kHvsoe0K9pCJ9dJYdovuvtolx6bcBmhA9Aidqnv7pWTF7FtXE94sJxkciZW/ToJnPBok9qBucDm717ouG+GXT7sJ2R2crYe+E7DH0M5I4relwhTEiM9W9UDivUACjH0XOj+r2DqCBtLP8yylAwO7v1djcxTb+9uUlHajXTbyVD5EHEHgA7fPUIWEC9AQJZyR8ZBX15Q1Ta6r2zPpVCdA7BDFUsLz84HYP1aul03YlkrehBfJN6FXiZFm93auyA2FwKr8siip29NZ4j3obnCV3jcvpC8/WrJjY7QmqNb2wfk5DqudYlBmNzaXX3t0fz9VrDwOsePyzv83cahjOwt/tqM7wmQ2EQ1qzufIcI+NW0PHznyviKjTv/FD+4bn2d4dC2LXU5+F/V6x37YeWjvP4F/FvNNScg9+NWvrsnnBDBU+2PA9ajJuzeve8Y0gnzUC80x7BhoSBfGTwl5h8/ktb2PAJWiT42OfSzU0pv4Pgur73Ag2a5576DfDZSW0ujhHFt8dNdoXEBrymEZZotPueMZZuYjBCDix9QD0A22r5vZq33h/0S//otPzHyU1DamPiH/0LHEc33zqF1/mmQ3NwNgp1XeZXeTxHyUa7f2Jda4ncLK23kwmdTWaG3zKJ60LznpjbMv54sPk6Yrn0iJPRVxyewNn0QY0G/TGvMLCj9el3ot0abR/nvQjPqeHJf36yUx+NodFt5OARwVpbhTLCglYybEzs2Eq4hAlVHjv2jajN0t/HH5Yr3jgenbj025tTQhp41a8Cy83QhAFS3FzAkA8bEufSWqGgntQp7dPzQvL4A1zfprECVWV1hT4S1r4mSIQkMBttTKM4NzvgxdewhbBwLbYuSJin8Z4zZXSZfDKJhLeOvtVlx9SdXpdHAULC/MSQpep5Ht/Cs7su3d5hcvBz5w29g5t10lsk54SqyI4RohOlgKCSDxlIGGok3+O25cEF4eqcqeVVs0uLtgGHKD/ngNm3J/JmPDgR6j5tkk/15akYqJ+BWmqlc+pls4TIcvYZqf2Xenq67XUD43eQnIUNXciXtCDeejrxiBSQzKWNDeVo3Va2WwKBUaOe5p4Rf+lrz7YCe4+Uw6i7/o8vuFSM1jTxO5O2I7kgW1cVRYOCjBIQLZYNf4wTkDfTD9Wh0EIbbFdfGsF2K1kztiRcMt6zMs0q+pjyfu5gSG73CBIk3f00jVStSu9nFEB6kEBg2pJcr/3L/y/k+7QsYa3Vv/otNxezCZ7ikbHDZ7PTpUr2SeYAOrsjOvrZf+FERGQaCUaHR19ey/OJf/6487TWVgqOOmFPCOWrXRyd3BgzW6441BpO1QVj+G5gNmsZ6iDrT6iQWqmBrUiMlMMZldUkQRUTD1K3e6nnqYO7m5IZRz3U3ROBMP4cNRnaJgcidSLOKFJcDeGrnYWrCtESk1OaxdkE0O5Uv52zHVjaEKMJAIHTwEgh5VsWMiNkxLSwzG28tO6dEGPJeEkZiLIaADvIgk2SqJHM4Xj7795BJMQiigZGXTki0xlu2GSV3ANpAQiHs3gF0cs98YhVcv7sGK+WSE/oq6Vy4p2qY9hKG0WISgPV0adAgpxA+wcg9lyAtjj5BfCD2sWJM6QGqBmuv6ti0zIgH+PF2DMWKgUSHRYMPiR+9r8f8XqRT2Uf8jvIPfZ1WjpammQc/HcfUpaL8PeWhDlFyA5d0TevIwAQ5QKpylMStHhOOa3X8oqqBBx+sdCXnbdPDmOX2UOAhq2hYKULAEUr/p8TLe6NmDEbdRGeH+ZmYPsUoijfa77/J7UnQJ/W2bzbGMXjXJFYjPGkRQ9pOJqCqqRMEdeB90kE//BcxyntD+EDQzk9++gUzwtKFfiLzbrt2msNnUrPEZTUWV4hnWTvR9xWpvW/9VHXKnR9Q/JEO5oSrw+zLXM1lp5Kc24p3D9mLhjh0su1aUkitoYLUGT0lynrRG8CoYVzjTUbeRPbWp3U5MZXdeDuEePfcHZ+dfjBkwOyurwpWKx52QEN7d4K4UQiTEaroN6Hj/lIXknA5YlBy6lNqSnqPC11iQLF9pN+yMT8bpEl2GJbk/co7+8nsoftZcsIWZlwG8cABJ1HhCt4KvNEQhysjFtFK3ElLvAlkyLhuhQwEaQzB+oVdOBmS2dvoBHzyieOn/HYentA/Ts044T/kLmNuFpd5dVpL8fyvOKd1ZPB7+I/9OkOnpgxa5VCJSpNSSgRWovliMx4xXBCmLmcaq095x1tplv2jY8U9mes5HtzhUZFb9Hm3TWt5G5l3uAmPG6CmGprbExyufB/rXyalQ5qOeTuNg+hFjkZ6q/F1R674oSerDMco8oeHN8tFUazFMGe/dLGW40wfChzNitw8wkMMNAvQGFHwskpZV4Jnyjdo6015XlCgl6KWEbdYxtFGu292Lq33F3PilmZGuWQ2yZG6+e0ohnLG8F5CZ2wZs3/a2wFkBP83+oobRHtIH67Uy5SqAGNdDM+pG7Y7UAPNUIZlSPHRHUWwkTEwMCjITA590VXwrdg8rGEJp5sfgzANTwO/k+SE+v542LESoAxaXKk+OgGo/L3MWiHBxQhgdfTWIyhXLauA+MV3orkGgwYzgbkg8LnMkLFHLCb1AZTZ67bVVzDKm1L8HhMyfXwZ5bXAzgAedBlh9pS6SdYBHcmKsS80GbeA979xkDKs1re8ZFLRhUtGU6/eNQjNWucBZzv2Nz2pHB3d0U+gxtSfb2ZEJDw5FA3af1rvA43c0msotoNyj7I9gUQtGpBPY37DBV2A60urRCcH1g3ZcoW09P0SSwCc0rIg+Vrjldx0uoU28fUXe1hc3aOLSNrq7fZkXV6/MbCJV6oCq49BVl3Aobkc9Enr7KckkADPeUKxAfob6cXNkayzU8npvkgAyBg/sswtUvsmxyPMBVuMKAAHNjQlTRqsx7OY79ngBb7666rlIpSASVnUS9tfk2loFI/7QhDtrkjWM7PjH8Gvs6+U8qeABZgsqDs95UQ9SI4QkPRnpAUWcuA5/9twYpK4jWwa36yvV7VAXM0pfjNc6v2264ssd2M4I1fwgTw04YfzudYKFOhTlwvRaXcTmiIM/hJLUd01A7pSsej60qXQtHk0vuESiWn0htl+Hb5aYmZ7TG5ebwC60Q76NqJCETAA/PL109aoiQf4EMpEtL22xFHjLnkDYmgF8M/XMWHARqdAW1l6mm3fYZAjF5ks9gFaxOOKlBLt+GHW+o/RE5bJwbnyqP1lqMh65XVYieXp8QFjANUQ3cnZeGSXhaE9y2RJOe75ZNc5w2mTcfPf63PDDsaeRF+D3mQTNmPuIYLRLBib14qNUlbn7pNfiWbywOUKgqW2KY6AFLWLIKmK///kQgkr+ojewLmURkiP5U2xdwX+b6fg89J/ip5XnmCKy3E1QsPJix/yRcrRdkT4DzYi/rzaq/GLzUxd71q2rVnHuPJL+algweQ5U30suY+oO4n5yvGoGR4lD7i8FmriG+uRI+6t53xx4jD3DhBQVcXQlRxOFH1MmRdrVOafNzzgNlYAPzppcCBHCEZkwk//fZ0cj7MA4T6VK5IsD0OJLLDlMQO4IWY/mleYkdn+GN3PcrxE1HhdP15DD6zyimd6LoxvOd1CafZD0eoTFJM4JhW4NYXqOAJRaNjw6ukwpzjfLdElbEdEzW+62Kz0PtPBTm6dyKWJHqGr/+eAeCdE2xHThhQyJ5rr7TD1rBuV83+NedNoBEl70spJPuWi+GuPb9y21yODToHAvcWTD5nrucQMyhwc/QvfQuZaUcNKRZtDxc9et8okoQLQ5slgSWfoQNBAW8TAbqe0MM7kWoHH8efPH3gzTOmoECdVu9NeiW9rwhm3HTFR7itJHWegbD3zTyMEKKBQdsALqU5A+0bvPcHHsmt8mJhxk0Lhn0/3M2DJrdQeVxfYxYSX3+lChonljZlLjvkUYOHKr1qYGKLjVV9o6m3Gaw+zg+Eu1hs12iHoVeFRTnSG+Dmlsc/+G8wHxeuFKaobnWF/KlYaKICGw/Ac+EkOYCVX4A94cnUBJSfuXsCrJxABrq87ZkziZHYfUH5dAoKUkHafp76/1WLMyQ2s8r44UNyMiYwP4jXxnQGGEanMTQWks3j1JpgRdndPxR/Qspje9muU42kfwkOyoU3rbyhGAqXyKvG+HSkTh8yr1tqdWew9sprlQFkEgCC5CD8slh0v17orwTdccUIlHodRcrem5Evu3isjJ6Zr33veXdE0Wal3VxeusykEBuc0yW/vcWAo2h4Q0L14QHJNXyHucu+Q3Cms42r9nW17TdsolEodXETOD2yJMFMMCCd4mRmaMl58npYZOAJCKDii2W61LNUldz/6EzeuzAl1s0SrhL2gLVSFcAfUl8ijj2nkvEys8uNzXuiLBDR8b3OzxjEsy6/jouNFW424eQ4FBk1wRdY0jUQXwY+DuavYVEik6QJmmaZI3S3lPYPQX5bmtrH96DKggFwtabtrESU4YwL2uiSXyGcSYwV3b89TI61l1I/RgzlqgfdxFRMJ+ScESXXxtv3biSr1TJFRm9fsenz03vN9p0MUMopkuEwcrJhMZs3/WLf9OnXPVIWCvYfm3Icp8fW1ZfZP1CUv3fWRqywPmvtvseCNHf6lR7nXgdlzw0DipxloTPvwM9i972rcZzUfNqatuAA/vb+pXCZbJcjwlh5D2pNesNXMXt2LFJSKEkEQm5yllqhTYWXNu/n58hREmX/cr2XTnshueGD3lm5lbRI5pz6kMNgvz9tyjRP+/LTf8LRe2nVBaKBOXP8WCBFGvvmGmYXLMENcE8E7FqXXo3jTlMbxmxMojoFOAyB724sfNM55Y1lzIEiVuWgYUaZKaJW7XG89i0gwCM+1+n8oSeikNAddYCsFS2JqpdF8UqMRVZ0y8zujPVJYB0A4M4iSMSofZgyZXBGhXZmXAOTPUXcOAQ5+y8CKRrzOIieBU1ZFNvr7wy4FNLBr4914MAAAAAAAQTmJdyAvBTWFDeS/vGoKsEQKF+FRRhh0AFKBHEAAAKPAAAAAAAAMCiRMzCjyd5S9fpIipkqgS/hlGzorJh/4dywOhlCqAKfh/iXOAAAAAAA7KLkoIP14JqTiG1Colr8VVHDA28b6dIOLq2uE78y15ZW9ZZkE4C7gAjHi34PZRwO5vN4GMYVUn7Bvc2iNXKUuMJPhYgv86+QQLI16GFcC1YAAAWJ9AAAAAAAAAXEjNugISMCe6f4yuTub3wnPYfiiMypT+6zNqZMfa2QWjhbGAq4AABg6Xoz59w2SAo03e6bMVq6KN9E+yF6YnnCcj/YtHyk3LuwTkjEyGtF/pUkWQD4WAABTYKCmiSi1v+HjQK/bqcxRF5Wbo8RoJOBNyBbBhQUinBzhMlnJFqO5GYmTRKc97MpHSuNmAAAAAAAAAGLao1agwyqOftHRHLfUtGOXLrxdgY6hJhMB1ap3iEHH9yUBoXAjTIXgU4B50QbOA7X0FzroKXw2T1j4VA1bpXH3jiB9fZ/NCka9AWef/+216PocLiyAVJDaFPVOymJqhLmuaLBX7YAAAONxaS97zNKrlTfe+yZdrWZ5J3ddDzKdGo3RKLrrvbiNrnjVSthAO/9gjFvl7iFJmgSJs+hJxWxFzmAAAAAAAINPYQhMsEDBN34nYCDjq/I0pHlmT4LF6wpzpFPfwzl9LvY7RgrqEPXhSh2WN9Pvulswc8FxjFVlcJVp/pAqPaCrGMxvI9BgSy52pUTNMIDHJTWin6RLoVoPXSCBqPuV91C4FHkDgdVwAAI8gA0ePR4a+b6uVeBxHONSENhu/6zCMW6ruDkQZs7ISvMdo1k+nNRKLHopKsL8O4aOAKAAAAAAAABe8WQvQYqpAag5pDgiqzFCtaW3iWVKvWFzG363g9Rzz/Dfpj9VMJpzN7X5AC5NALA1Df3yerKyh+L362YsR0BKWXY3NZ6+DMxxpxrp+LUcDs6rJJq74y2Q7vpU630hinlzW5nTcNoAK5kuFHxMA8pHyHAS0AAKcGitnwHG+7Jko+aNb0P/XJaDU0Ev+h3hJvD6BRI3Yi7hsKYUVDQMeMnnTGo3p0emzsKagkAADlA/whQaWAAAAAAAPDtrwFdaaaQJFOCdNTqZ4N7V4TC104swlgXcUSZd+3lC9rSD2Hpr7frutUOGruPTqAJjBDVw4BnxjZmjewNQSUxoQSNQhf8J+68CR5okRPz08CfhvXLtiBbjYWdiAPgdyj5GhxLUo1xcPtrUQrxdLRwZcXoP7m5QfA9VljbKWki8TZ4Sv4AFyUJhBPjwvEVYD6Anpm2okqm31zrrY6DOIFbIkJ0dKiv7NwqAThCVPmsoyJHbBMRbVvcndC0n3m1EAESOM0UAAAAAAAowNnMohhyOTpaUL4XZU72HlOWFtUVsBkzwnM3TUFzumO0y4it+znVyJFfUWewFlhxkYncIAgIimRxgAAX/qdAYQByiA82mMUUpICIctc1GbIPmuvLSTwXhpup4SYqt3+JSP2MrBKe9FqCpTcrj21MS3OKD8H5QDBuwi0e/iThEyc8xsOKlMDD5VPN6ziOnG+EboTq25psRS1svkHyPR9YgYYglMYp2h+ioADYCipwSblulFpBgHPx3udPuxjrgDQBlZqRzMknxdzIL9EAml8p8nH42sjs/SOdPhioqdByL9Dgl/fNSnikCqgGSctJQAAAHFvnbjMSwhouHTEoujRD3UeqVOQcp9e2quGYi0aBYrsMMfPby0/nmO381Tz6J5ycrUAT1f9qtS1NmnmHyxu9mAjkTyAP8133BT926ULwKz4+C1yeA76sf5/vnCLB+SYHxI+PbPCldMAVkTh7dDtYK5Tuj3cb/D1+8YIMXipl4Gv7K3R32eSUl08d/y+SkeLitzVcCogfrh1s1wUzlQdKUHusks4pwgtPuBhra4BglDq2gI+zoYOM7noGz7nvrTJcqiaIb/bSSJDKeB2X4QR9ZJIJlaLPulZvahg1CcKAMCsZUxzJVEaUZGSo6E9Kfdmam8YEYvXmdqaoHnRl+kHiIMpF3G5ai3HF2jVVvJaFCUB3kJ4YkCO+B0bJmriQrq6/sJSIFqgAPfXiPgAAAHgJX2ANhM7eTjJ9lYW5d4+Uogunm/ng9ZkXpCo5pziYmKPskIdrraKjlU0xQHrQGdyXk7OzBvM1ToNXkA2XmqnOmFJ5MV772Y4Tx/YYA9j2oi5Th7GAJsGA088seg+rLBtJwJ6tC9Eb9JqSZ7RcZOhGPF5Tq4uRij4SNUQIza51546z63ood5Hd7xqXjw9ZogxFnvgkN7V/slz6TfQCw9heUahJMRWUvoVVCXLny57GSX80ZdzovICVLjBKzN4apPLV46NlnQhfSJt1Alw50/9LZL11OnH7An/EQ4+Rv8VAAA3doj1SU5ZhADDLRQYZVczVwz70gLG6Ik9UYyNw54UYy5q9+ZISg9L7HYYVzknsE9Ub3rKqFWAYsOi5mHQFOLOp3JB3UW2kA7UTCAufl4l+uWAHgsYb8AAdYaqnC2KYdFFgXzr6wECNkmi7nFhjImqHu6P1nHHVuMu5ARrhW/1MaToFkp661Fv+wEftXxvoI93+o5KKfp5TJarWTLIvQKS8HiTPgHToAfOACpINtN8UNzPlZ9JNFMvy7wN33mozyedwCZoSpSRMF8ttFUHELrBoAvw1DTIf8k5Ijgjs974jCl1t1tR0z/It+h78ns3iUdUyDh2Hy8j2nUhBX6B7aradMfL1hprYgcACVt2kXDEA4zjqt6WsT/cGY6olrKY/yqDuvw60vgcLMWLpS7n+52Vg0+Dyp5/WYkfolbLBljgkAUjORGtDqizcR23EGxUSS8Q2AWHpMQnKXq/C0+qTNrNBGtusATJI2K6RoKS65Bd1u4UQ/rJGGpyc1qLOc3uRFWSLlRZOTVxRtntkXldXGzDFmtLtFRs4EeRRdbZAAAARxAGNbrEpxZ1EIvJmhLa3mu/alMxRv0xSngZwrg3lgjK99jOPhlr0Ot2LY1gP6P3YUCbp/kYjib/OMz8jpDXMMh6xPJvqM5m7s5o3hskpcKn0kjuuxsxAHDbnoZ7xhpWs3vF1b60Ramvs+FStPfjc/XjNtbp0n1aV1cTQznMmA1UJrq/xN4em8xFzgoPuRw6VWorMt57pqNEF9D2axCr/W35gFMDxuUNskc5YEVW69qhPVVzESxHejO8s4SorMptvWfcldbY65zGcmGLxYcnrpXoE5YnegRCER+kTWg31K8BK86CqGQjT94TwgswI5ANcJYAEtQ6c9y/TYgdueq8LDp2AqIVhq/92ncX0Bs+b9QDEmD7mFJ7AAAHcgAAHYPzuAq63C3ZUid3OFW1+/i4LFXIGdmlkjeesWTkSIpua8qWrDG0/J+IPA1qiFxTbwOdCUt384MGwIDVaT34AzQ6AqsOdqaZ9z/OqpLvqJskCwffhWSWvZeaA1zOsIJ7FpPCB4UhaDIesJmnvIv6P71lxcZgVzABnbnUTEC+E5tNGEwbJvPR7rIj2scgECGt+311NMgZ3Zj1hrs0kRX6o64BsgNPCPfKjHm/PMHyTprCFnuNAJtBi6ZlTo1xkNCEov3k0YzQhnI177tZk0X9ryF2csAjCA/LZ0otNzeaqSZ+7PFzmtNJXxqvZduB0bJcZC6j42NVKlFq/30V3KeMTwYJcpVwIsgOQ9D9xA8BLEJk4MIKogP2mnjCc5lqd33EbgZPxzypvgdhojfXFS8NmALnA6AlAWXUT6zAMO65gsbK9N7h6rMloN5FyYrVlLqjWLgEUTO/Cdy9DHxLJ4AVuNg96IyGS7NoZgPv7cKwr05HdGl9b0bKBssad4/Kmg7Rxmiy9uJi4AS/e+uBr1/8cj2lB7Qxj0ycjyaOrrYmkOzxdVwAQxsWOckzDgkRbpf4aYHC5hpN0FBa36BnYkTAjmy6RJHzlYubJ7MwpFc1McataLOmD9cI9o2wu6LvQ1ieeJXuBfZCrBJOQSC4brXIO4WWTh7yyeOuAOh7sAPj/r0LX7Osqb7PAwQ1nm+SIugVzgrhzasmG2UJggw1zFdM33LktmgrzrPDmw8ah/VzF68+bDD45qmbf3KWvPWlmA0/Ufkpg0IXggfvvgIMohhCrAAM6akJUgB2/vEeo3HKSw3C53YcVBVuBs2IbBW0wHe2jF0kp3xhqy1MTV55mDOB5MS6ocrOHpCmBUFW/gP4akz5qcnNd/db9NYZNLBvY+hctRpZzRjPgf74jStDw+gaKPtuabq8pABftgPyBbyJ892x8ZronGU+8mfGodggUjrl1xD3wjSQCPKPM0eIXPJ1MKR14kNcscxZ+HyDbIhlzYt7xsSrN/ecXlrjwEmyM5WjMYV/jkQj1/jrSMs2cktBi8+GlB5bdxiTyAwlsLoRdPnsGa6dhV6B4nrkrVzvPh3jDVY2k5k0bY9vKVyGPeBlydM4PM2TmzvArE6BpvsUOKewwGsDrwy0ZMPUZZ8AqVQwlQ8evJqy2s+yx3P0ON8DQQns0XpHUF1IAAP9rFjsmxG+CDqENfKLZAkUABiXAaGAvMBoU11DheZKa/nqa1J4XuWfcL5mmQcomCKVHQLY86cM4IqUg9T64r44ho1UIAX5jZNC3RtFbq4mvgrvQ1QGV8ycRJeclqJhD9wLQBvY1n7zcj+VB6sPhkuwL6u+HKTmVXaPZaTCwhjC6kSzIXYbyhPwtVYE4V8BTJixeDx1SO1gp5KWkXwoi9D7tKUL3dge4RxRD2VW1NBX9MOgNqlCx4a9RkqZpL5eqxb5CgD2PALgsrc8N23VcH+tftIFYFsXQpgWSKfjUDFnjhB2eLrA8mcPEG5y+fNdtKxwWy1p5WT9V5zaRCyQH8HDnBDvA98bqXRRC0jLhH+ca3DTwYSeHj72d/M9xCN6FGbSqCI7VkPnmA4aE1tb+qDHfyyEHwYW66C7TT6XJgZ9COG6Y+YN2UB52lwA/hXgIb1oFHjts0K48nzHjXsHShrRumay4YawAq0Wrn15i9mWRJrMSFS6Bgyig3o9jFDZSQpXLiQljgvCG/Y4dUAABLkAQ+Fc7zIor+1/rsyFq/50rXyU28Oavw1nozRc/BfmvpygMOAsk8CsZBNOXuEs7wyl3H90QUF1fN7PedCAAGIu7yAvejNCoLXprMxV696O8yPe+2rvawfYOWJD8XMCRYv76NEf1rSq4YmssbfWBlKzAPo17yxbES3vFr49r3pMqf5qw8/LJL8BLzZVkSzWQvwcvhlwfNV9elX3L/sUrYU48XOVPoP80s6TWC7F6Z21v1TSyz4vNXErDZQK3Naz+8fmMXTvlp/oa58RNmSNwHa23EDS5QMNp8TXkSjlZDKRV7vYjIVbPNnz+v7+HdNT8YW3Tig/ni3UtnUQwmfdqEb+9TVtqjSzQ3Ex8TlL/eiXsgIg+OccMW8ns3g+UsQGg9rxeJHyjDUdX7Oilx+dKeDuQ3t/LFniMaKZBYPoJx5lYoaMEbqgr+imzUfIhGlRNOX7m8pNxk2rULZ0/Pb2JjvQCGcIA4ABsjIHC4CLNN5wWZnnRZgfIhjemvbPoSRIOpX7xFXWdv8MQ16AzrlzBcOsj14TGKfApqhuxA2ZhButEt+DRbHIyWmNO1CT7re7iFapc9oKuXvrZjpaS+iMdexOZ+ZjerB2FoR0BZPNHHzqSXbO3MagVUxP06zZenkCCAfe29VfoQikrcGrJQZ4Qt/tvkIwibFecT8BXGqtS4t8JvgDQWTquf9BMQC61iIo/Z71WKTgWgHA6+ElSg9yqw7uWFtuMkYYLV0FOmyYHMxeBXtpfjt0YrZSJlJPxe+qn6YkErIIKFjYR2H87EO6lixwkE6ud/B8fH9iytFS2Rf/GbvTpEhqIia5+kXA8SN8oP4mesNLORzysCQFmqEy03mqizZ9uFAlOw/d2l/lgMr7cWpNrlNjGCKXFQsBQXZVIR6zYm78Mh8jkSijYxad8JSlxKSri70MF7e+xoX1k5PZaRE4j9HZclIXF0WTh0m1nqSSg975CXqMAIxQGoXB0Uny5tFpgnw8d9G7hJHGxUpGB9NqKYymJ1SA8qQSThwXXBYXaNtTiTKcux4XGWdmfH7PZdWGyh75tRMg9Wm2A2H9ooMfkSjdAAML1piA7Q6z0X0bg7l+wp93BMviTzeBjp66/JPfqoVxhRwadglIfvNroJJ/Gz46wv9VBXUrZDBUt+K3x0A2Q4imqeNYFxjGC76hl1CuGQIZxC6BgtcQGuuHg/VCgQ9sUIP7++3zrPnvsBIInY90f1jKMf2zPGZXP9puqgZjeJyMOal+yrNaPgeXNHiob1eWZKIFfWIWUw61R2bGfEyUtrqNsppphjg4ahG4xJsSVK9KhOaF+N9AuVDIyh9cC1Hjsgduh2Xs0vBi+Fx8g9IHdwROYUVRqirjXH+kvcM34/a1biBYwtploIxQwgM+r6+S2T4O75x93/qOgSqgcNyKgbH4hNLXbkZ+yeGQjZJMn6GztVilKRshVYogVbHaHtDluC44Ly0eMAp5IOgYNw8GU8gKRZPn0cYA4OSCbkT9zcHBKcuvnC6YIf7AaN3zf3ldZuMK7ZplHdYENj3ROmawtVkBGtClAjXLnBmw4KztcUcM2eLTzee6SaJeXV0+qSefMFl7Kx41lf497lkCgVyxO9S11pGyd3/r6KeR7otTVNQTbz2JQlh4hyqYnoWcnAGZGsJqxg+n9MAJ55ZaesQAZOsWBWdA9oedE0conxLlDYjP50oOV6LLrxEgfl5CkvDmN+OFPGkkz/nd9Xzkbm6dsPFxS33oRKLdwRXl5iZsYHDZgKugcyLWydIToAw83R4eQYBcGrFhLMB+a4J/GX6GoBufst4GimikqDCB0j45luofZ5HCV7R7+7Q9hjUhlht2C/i+hP10HMlB0ZKBxXzwhID5pCqnqnO1Ujg166SqBbR2pHY6Kxq8UFsGT9Sk4mU6TQA3B4+1ck/k1XsVqHjmimT1DnevL8SvgzFebQbHFRQZiQENbtly0lWiYXhA2nXKSWrwcUU7oeUTdxWPExGqjIlGzV2jm9zdFs+as72Vd18z9b9+JNtI3ZxpsnLEOgrIWyU45l8777L2OI9sn/NZBhaX2Qs6Vvh+2SMpwJgFshUx1QSkmTOXqmzPcvStkP3Zp603Jdvaf+/aJ0pDJe+HrJLUu3SAzjzkXNhT6PQPqPeWuolq1Cf1XVTssdCDiatms68o27J/+umSn1cbv1EUsoAA3UH2FV26JIVJH6Mk/c7RcHcdoF3Csi6Pf4cDALM57VvxNBuGlrzy6xdM0Q90KE6m0BQXICshK73Ea1OCgdvQr5HoZuKceHGjgAS2KoP9cJI8UkgXCHesg6rHRKoBRZos7dRy9AcMDckfhWgnQf+wIdTPKY1WyGsajV27E3BE6hBVviV+INy+sklhBFLNzz7RJT6+RiQyzTj9VTYFwSb6LKZlnY6QKqyLX4fneGaH+Tic53tu0qSelF4AnUc3yOedFI6jbci8hVUD7iBpsrT4Ie11ehleN5uIjiP4PBKmH++jJSmQICTOCVfmGX9NYNmZCstiuPO0MfZtuntEWk2UnkT6xnqtpzJiG1bILJvi5PirNb2s+M1wZ/6waEBrWK+8Ggulm+gr8lp90C47WC7zR4h+KPQJL2j7m0BLgVPnoyIQaNRC7PzT7mjd7Sh0fp/izQJxCVhjKhJn4YEyxF7+bZ/6fQm85OnndXTPhxPMFHnDjk8hDH92in9m8T++X3VpUXfBE8JnBEAabq154TXrjT5zBXsNUfqgp4ymYtWyV8JfcaznodD9M3bhP3CdL+6UrYsA29C4YFr+PYB8xE11Z8cpuCpS7JgrzwUGHxJvJaarw+WdGlCLduXd6pBFaT873ryieGjExlEtCkO1p/VFC5x4rTzK9tMkagBxJWeVyWdAkzA1STOTbtOHDzrDQdcJ3qKatJ4QwsCeUnigwZstnlsAcrYkQ0RNkaqwIUIsTDqewO6urw+ATK4yWRI2jcXGqMteVZroQX1K6XCyb3NisNoMnYRRA/Wt0bs9nWY+lDsw+wb/1CoYLsKArjz0+pweYKKhdef6HE72DCnjvM80rRU72QIOkTrU+nzTfdp5XQ5XzUdVt6hBk4X5nxF/cyESQNgVYAzpZErhEq0cbjgWVaByeP3Yt36DGlZw0iavbSQo9fubK3Xjs7exwyzGk1UwCaPJnIWo0tBgqE6EEWWuTmOL1lHieBTcbq6p8NWRN0tQr6tX+2TxREQYsmfdniwYrFAnh4CSGtVJepokGbGC2xHpqNh6TU8wuK7NYjX5Q10jL8+e9YY7VXXQ5V1ACVdcZrHIR6bZMVR866Fy+XzWbEP3QN8zFbnVAJHMLuvXKN0qYJucgU7noNM/xgtu1w3bk//e+d9j5Y5YDsw6YnfYqFpWkp82+5TLqCZFOR4+RvGrclT8lBXco3qntkK+vLHUGQmv+4bM4Z6XxrNPX2+m7jd/G+6GLuXf366StV8BI+gqjhCCY6FB5i7xVOIBk1R8nRZPcLesV37j1oLRZkSn7gOA35B1QKkaXF/9n78eH5/W6FuIFaOWyceRTch/ZR6SpUWEvjYF4K49KIaMFLFbi20GxrBCLOfVCxezKOW/ymMdQkrEw8dFodXqf6qn1HD+ivlekvECNPDLGlD9bx89zvzbVZoDlS4wZr3k0csJ+3WiW6VH03DxXs3RHmg3jhqNNDjpDOoMW38TAXw3ahvVxmFl52LZvSFeKUI9Qddi4xyO2JESaI61/86cED3NSgNld60pmi+cM6kHvOZixiJZbT8zXKbRW/OvVCtoCzw70o4ch/mAWi3NIiELFGtaVCffEsB1xFyEr9Us86nhVzJMDdX3xkARBlC2zGKkwR81jetr/vxdDvdgISF+YJ6Fd/1iv8xvFx0SoG4O5VqIVRko/0dC4PV+U7yFKaWxPrutCrfGNHbLTW+8z3aIcn8wO9XbsYA+7s0Mw4AAEPhoZIjWuPqKfccfEOaoaJJ9ROnqUlUMXPCA9RnfDX3F99lrs2vinPtrW9r+ZbUYnKYDlBhxxm6bQZmAKBfWzv9dXznQdzC4+tlyqvFqaTzjnWEl23G90VYUTwyiVZVksvSsUQEExmh3nl/bpDf6xlWIe01fBXYTcqiUKBKe5O2gY9VtwFIPJLdbPC47/qYN44hIv9viqbvWrEfg1caevbcl4M1fcSX7E6lMfV28mLAwz1onVsxSyw8vIU8dTYJLMLJMBzLZRQizf3sOAZdwCH7rVzo3qRd3SEMdUGtdntE1zeI7FlCqBConhj0jLbBvd3fZtntnI2x6dbudB8YcTeL0G2R1A1qiYwHiOwGZqLDPi41rM7n05MULoqYiQ7nZ9CqP2xQNlGA340R9EppUn8SL+TeoY/15VQwtsqeKjSfUCUhCyxiuD8W3Piq4rXGdQ7AaLk8z+dgUGRV7fyY0AKtbV7c4kHrJvl7wcseyhW0AzO0YadJNoyei/MeYvBXalgjZ3Zl5eaqRClcPbXxyNSaV7aj6z+n7j7I5ojw6mEjno7nbpHUJP78+SDxF9JQxJhacqKV9Di+0qYaBtxFIPQuyWFbxeXUbXjS6V20fUDfHXpxj3sxOMzEzkhYaddfkBQrMZmmPTlDEg0A5hiZCc9Q8n/hn4L55bWmIEr3ZrHwYZq7bJIc93cQ2WfYHVOOHgy81YWNLQpfokKjIIoagBDkPFbezrKdCVOAGKGOwBW1aB+nsOzGW9RAJX177VkKnYTqVP2zmWR2d6X1ijzdPM5vRhUPW7hQno0xbkDRVdjQAHCwE7xrhWQopPLFycyIvWM1TS5eLGhjNC7V0EtV1NOGtvltapLMxV0vHEr7P9zGZP3upoVNkkzwRFHxFhHJ2qDgL5s9hXRY48/is2AnplahZpIXrYr1hYxZwOF6/GfvaHc21m/UD6x2FrO0hBx/8qN4Fl6tDTvoL10xIGFDxXEgmCQHqDpJxTJTPoBa2qf9zi5z5JFCHY7Bp2RWyvvx6bf81ltFgIjch6HCz8g8dODlH8kWF5L/vghKhj+rFmUkAdc+hR7QUpkhpqKbzeuthxu5cEWXHxDmNOXUN6VaSMrSI/Tr2/rUCjFpsSWhK1tL5Rs29w7AGp9nymbhtmt/rVJuoOS89/528TNeQqfamqT7BlLUYXxBJuM64rW4OqY7/lnjvizzqUMR1gY9UTpWQ9fUIc34CL94+Aa2/C8Kn34+GB54RTea1I92Vg9y5wLVtTif1YPjgIdtXwYAURqUz/uHCHq7O+YryZ1eHfOqLvWWhqm2zc2kE3Kgs2bZ7+pSymUyo7LYQyEdQWDIc3h1pCfZe3P/L0zbB33Ne/rRiSQmaXy3H9+Ll4E+zcaGajmkJ8dWXHafg2lVZBhsnU+qNc7jTrulXc53gQTuW2IrUVr5pZ2BKeAzzXtuiBMK/yUfW8w67ICDJNQl8llSSCUl8ViKgYY+PyFzhgofAmQ6BqwDh2bZq6IPW34ufsjaSfL7kHcdihqhRDjBhnqV5hVtAqhwNFZOfWi4rcIKgFUyMbajOy25+zw9/QQhR21XII4nIOn19C28sTQkQf/DVQ97ItnFLl35w928fI+kq/rsZmcfoCpHF2rRXxlQwtdTrZrgG4cJLWcdKekwJLqSc7jT9NE6E/Xv3pfsZmyypZH564Y9xNqHtxYIn63aLALMVdnw7cX40TOTZbOF4ubGD0ze1fx9VFDN37zu5At7vg3/mb2+3iB3V1JWCywFRZ+zQcGJdaX6yk3hLMJkmJo8gh2H3N4G/syS0PBsiKUhH2+p0OfK5zfQQsUY2gCMPzciosJUTq90iIUc+HgfDKEIDzPMSN2GRLHT8EM7DjFBhiIoEnaNqOu3kqFm1Yhn78CeYepWfxHUxx7JZC5Zi7czpQdQvQlapyEtZS+C3iwcoQpRl56YBu9wVeWZqW2fF6idZ7ORdO+cuAXvj6hGpBGqoBqqqVt3dOnBlrQSFXdkzHK371nH7ntQBqmvq3qVvyqwf4xrRTYBErqHtSb0k/4TLNN7F/ni0PVMzK3YF9t1WmATDCDkeGnSP9ofv4p4cqktqCsM5XfX8quWcDG0Y8i5S8u5rES5Tl1W/77eqxnZZlVcugGi317HqZ08e3Re8MLzLrI8A601Dgf4fIetxB4qunehHCMnN7TEDTB6Vag0K90dDuUPzxcnyuO7kK87YZVFGIsr3c5h08PjqQmsX6SY/Ei+mUWvMNl+S/C5XzCm1ITOCH+x23IV3z0twXdC9xX39ldTVIx1nVATT5zKedh/KHVogF1NdqtzaGIuqb6c00EREqKdDZ1e1KBFmS+fuiR8kOHir24zsVjL+6vxKo21BAT7DnZ1tcFMkBh4MbgyhEaDXeI/gymsh8PF6/1RpmGVnWoJTmlNjGr8NyrCf79zqcZbyCgaNfRc+mYCRh9XSWMlQe53GhA7mtn7usy37+1VnrFE492HYvAFlXiCpeIZs++wBVKW2bK1lJGFCMVBHPkXstc8NxvQT9q+19hIUik6pW0z8liqJI5Zk+i2sflbtdvFAf0/EnaiRYaPw3E5NpPz6Qhkp7NJO4YLbDRj+RZa+LujyvFjl3RggBTcCtUWp/v20mNpY+1s/I2967JhIW5aNqwFFDJUMOZ8sIDOkbKhaj6uQLKw22JrlA2dF1jHEM/Ifvlo/IObgW8AyJKpayuXePn1km0H2lVCdrP9k7r4dthiLEIr6Y73to6Xw7B4bgcH0B9fYM75khw8yo2zUIkRxnZtRDp8XSNIc9wxvAX97LsEyPIrP96btSZe5par3thrOreV5/Q1Atc7R1v0A2SaN+yRS8ZP/rlhI5KtIPFUEwHdFy74h3fS8VGvG8RFSMfcSXYrvMIpVUypOz1vnAM+TKLV+CBWAIzaz+pCe+CEGesMbwP7k3xqcjJhx6d8UE9LiZDDq/xfbvMO3MW2fOMR9XJJQ3UXeseMW7+tEOX8NREp7j7tp40NeKy+f+yF9lZfQAiE52fu+mx3OzePQF+jJKKoa2LQphCZstLG3tbmyD2fUKlekeNxsoUXT/B7nGtC7KPlNrvu1L0JQK/YV8pOL/RIn8lzeYpT+rul72tGjdBgDoRn8WrfQRML96971+SuloOSTW8ivqylgo1016SpNF7hxbulJqX4O1odV7lTBzicYtPHZv/zWz6rI+ZYz/ibu1PYZqa8Ae6QcLXCff66rFWMu8zb/4EeGYKxSsvoLwQzYB+vETl4JNzmZHDrKcHSOz0J4TB85kwl4PjqhmgFyan2jJ3sZnBLjhklgjCuj8LldzyE4kExl85/Ennxz+aAddH/OI/0mR4Jav85i8INRBWNui2FQUlJy9Tk1aPI1HKr8KLB+BDEkVrvuRyzTrSeux8q6wOfCrRMR3myFCJ5sRwLc5D4mg/zIlJtiWzAj4fVGKVCrJMd/mlHZYCdyyz7KyB5uik+px9Ke9ESF9G3219hHBo8IkBWqT8uSO8Pr6ag/i9nr3Y5SDEnIsy2x0X19M2Drbo4HPZXbAfyYil+AvaPoJQOFz/z8GZfn+/NT4nOLiiPdWjj7+cgbsGWUsrxRV1h6E0vLMTI11t8uSDSK7CctZ2dwLlOg0gfNIApUTSz26FiFm7OSQFet7TIEuzjpnR0b5F9EiDnSiQQCvbSUpvJeXwDKFsckU6lEII/FzZVFVpor9+W/LQ/tPlWBUAjVCSv//UyLDFwYmDZEE3GeI1Rj07/5U0xxGgdC1wPMpu+PI/Bvti0SCXet0cR2eb9JQj4bdaP/0c//YrXGyYNPACniE5icj6m1P0/ArlzFfMYFoGg73m2n1qfiI4fFAjMO6515MUBX02YX6RcRKGT7sWSP+BDqk983OnhN6h9ksvgOjpbqSq3awEHzlMGc6dUbP1ppnu/w+nPMsHJm4nhy7jmrGyrLHcF6NBVSNJDyzeCuggMAVxjW5+cLOZysz6kym0BkIRguA14aqIHR3o8d5SgyCjJIg5OVp8nisUgaOE46ZurJ6qSqOKNTO8koQXFM2GDBQhp2wFcuZzC9CDDi8hPjMG4BnJsVDNfphCCSqgLpecrlggak2b8NbCYO1gRK/DwQq2ori0KOZJMsQNdWJA/fWBRZXclKYb56bYybIRUqPfs+PURN+tQZCpCZofxgJM7fVhYpptkCr04swK73QUZf7haAB4i26dJpAx9RdNNsrBauQVclMNKawaxzyVHHxnE1Mk3WuqO+l922T+/Sw9FuYBFcZc3tJXENfQyfJ1NmYtqxP8/BrVavcWMNG9msb8k8ibMVJz3GgzcgW86rjhVhary4tRbsLcCq1IarjUOQqVToBeYjMj6FYgb7tnzNMkxQ7PtRuzOLBToKX/C5OIy/1HeSQs1X3PnEA2ERS4BtcujIAx7xcYc5eMeJpaWAC9ewZ5l6skunf2u74/AN4KbkhwmFME1JOkwXeh1cH4tdjSNtvCAlm/wew0W0YA5NwZjsJNR5PVvuInZUQpOF0qxbo2YFjBFFc5Eqicwl9p+f+9ROFN71kKYYg2GSk4gGcpgtPsP3XPIo7wFYgUKMNq9GcLIoDhRvU/oEC0PcuW5Eyfjdv2pfAqpZojDa15/aUaJIaou1fQfWTf55Kf1Oebc2QI2F4AbPcGU5j+56n9iZws5lJGypuuXrKHCdNgBRKj6F2jJISRWtRKrCY3lanOMV4R4ntkOTHzkjxrlxkqi5hALqWDDE5E8PkIEgoWguTmKOZMLfKxvMCr2JtVFyQk0zbAghxPXjDSsZp5uCs9ZdwSXExtLAiBRpVaIqHDcW+q4KHm/+bUfsqFgBE1by92qonCvXDa3ZHuAs8/UzoJI7pzpWet7g7Ik9ukyW17PfG4xNvlMeYDtxFFfw4Q9tOzJza8kLgBF3b/PNNVWm7tsJpaFSkkhsV2bGOTmxyMxI5xJCATc1dDkKrsVenrFciqPhh1J2Z6CeOjlVuL/J3qTMmH4zZEtXv9znQU2QhT+WuKX163q1LDRRXm1N2zQPZDlmpk0n5Urm9imPwqRSuM5NMJ8QfCAZEoy7Ns9/kj6H0rUnmrQxrt3oeR141CFwLpLZW37uG9sefWiO/Xe6lkUihbePkAQ+IzHIa2FmsogRGhoxHihivxBRT6i4TO2Kw2zCVla93AcAN7wWJI+jM5IRDNFFn2EpyOTSuO4iHM4hED7cOKcg8PcXXBR+of9/SPnm2xSUmLnAehS/Pihofd08aEeSj2VMscmAjh12qKePeKFYuYVRmVljfbOeQGZjYJTE59GaNf/3PSegZZq62uY9S5ZyZTOiIAFaRIQnIrAParf2PQGa/LYCAdrB7tv/gbFqmRYuk14STQI5uRgFTUkBw3PsKDoXvmvPXHKpumnThR944yvSHzgCuFdpFaz7Kd77nAO35cJ4s8lkQ50oYKk9Gb8Rz3DJTp5maS8JNbl4lAjxliHqX2a5EqwSinbS7IuLSLh/C5gf+kk8vpOV8YZOBAhND0HYEMcuJ3X8iSFtdEQVePWDE5gq238e5CQJ3WuHcZ6+3fFqMmnF3MkSU/loXodqzSwpi+b+Nu5WH7xIkrCHkieC+uZ2BmsOT3rq48MccBnWyQZQL1+XPG6oSQB3pylNWQ4mZMCHgH+6m4p/pr2l6vrkrFZ+UE1YLEquuUgH3d52dDUQR66nW3wo6hq/9CRcmy3m1J/2cK3WoY0TUyCe01y0pZupi563RVc841h7JVq3jPJWRCMl1HZPSytWRA1fzdEh36UUkbIoDLNlL4QK8hVxmnJXJcI7vGHGr+iovDlMA1oh2O/WXMYrqTKo+/q4WpO5mH5jNFjuMvRD8fJy7KwC/IpSDqFak2yyY1mH6zBMKJUTLxDqiLXvM6qZUIKqXMdEcE4ErRtl7ugc4XadQ06Vu2E+XjoT15EZknzs208yFdHdPSWCP9pQUT3oGPXjiw68vk/CykGxzbKaXTi2f9PdTvPFrEI00l18ltYy7alpavEVk1GrsKaYTksgOLzb8iqLCJuHDDsOQc+sjQ4Mc9jHNEPWRBy2AO5lSCNtFc1TDOSdkD+Obu1tjSq0FBFSXDYfz39ht/gKLRXwiCbM8jLpnuQwUAf5pTOA3PeGBTdilcMvFRr9+PkWVUCw/OXEByu2wEOkm0OxTPtwof9WmBqjgaxWGxdtvEAgCZJt4hyRNuZ1EVPv1nQcUhlrLeeBz0Eo2A3QcOi8ap3RXXP7P5GYyy2c49Fbiu9i8wnGBMi8svFt/dWLJY0XlY0OzDjbQftThC20MRs/lBXlVR7kSf4JDYdxJDSkoD+Yzpi9gARAbG5qGdjs/QnQVv43MXJdJlB89P4AI8WMVSPpMoyctD2QjTO/nr95p7GqOAIMLFXWBsownMgPnJkrM/jDt3WRr82xtluWiIz03yVmm/vOtyiBJS+tft1OvhK6kSbtBP8yME5XxwtYM1E/d/1/1c1yEIj/cwvTm5CI3+uf24hHUVIUMl8z2l6LLYKSSMqULNez66Mcl1OIEJBQyqwV6ofWzmoXl/MYnhiRYhc3sHBvjK8Uy0egsQbtfiReJte/zF7+jb4h+T0LVQj1M9YIbKQfbmiCXtzyOXChkumd/uBmn187fUTnZymrMITjTOUWAdC49/T/KFFEaqKagqsFA5G17I547RF6r4wK6BeaA6lkHaecmXZC7nJ9OdLpDUfqAmU6C9Bdz3d+6YG8MIs+E21NC83Yt1meQXZK7inU8ZWsx03/28LJRVsl0Ppkuh5/lCqDDp8PMj8AxaWiUoZHK5IdXiVCBB/kemiFNNvnXELd/zcaFp0XEocuHtX3BwdsHg4LaOv+m6I1k9yaQU4wx9/JCYMadwYFwD4PpZyixWIJGsA7N+065SvVdsBFXMSAt2rWETaah9jpe2QvVCySfTzmHUbr0nJ+i8QRSf5xQr6WUXEPoGZY0J3WAW6o7LarR9Yvfym1gRxMTGX5wipBGS6h4W/0ISWRYtnL59hxxifzuuFT7Jif9fo5IuQzJtrFxyuLVu4D6pFLA+m/OoIF86SYk8/B8YmKhIvhBOUrcK/881jek3NAN5DDo7Kc3JlkXqoJxia4Y7CRblmC604QqwnbwDOSMa+ppfcjfvHTfc6iyWDUAD52gnCsqQNoxhpB/4pG6mcibmaWji1FNxEsFHrzAxmaoHxwrUo4QGIlK7JyBAWE5NdvYwywq5PMLFFJIr/37/4ff+gBV7L0i6wEhvvAPgQWNnQUqMu29OG8iedRX2kmW8unqE54DK47b583kpNhLI6BGcqSOKzIhT6e/Dcb3Q5oF0H2ifqTJSMy474VvT8OcQFtYaUQ9Lb+C43EodRfZbFFtCCiVUv4yyjBL9M1pMVOBN3Ta74e5HVBYABTs8lESOaNDB9Y/MXlB55wA+Ir/dA1jN59h0TO6N8vvX9HqieVtaoD2LO8JzyG79peeW1w+rDM542AyZFjGR+b3nMMJb1iBEfEO9hpynGC2ND90Zmy2soxMqz6j1dQ4W4jXyC0wLwrgDl2SyVzYJleGMjAyDvvaz1Gc1MIn1SMGhPWJTLr7HOcl09n5UBAkOutXpfzSACleWHlQpO3Ks6c+AyMj4pTMSeiiMHKeb6W5Qm7BbpOoy8nQR0YQBSbiL2cYcQxkTx16z/w93ezGuWwwR4bUsYN2ahlS9WDHyXlWzhY3Z5ha3dmt7epO5xYEaVKYOsoMULRRNdR1T3+fjgCdUoa6Uz2xLDyodZHt/vq015RxXlB605O8RGrV+j0wLgCQDXyjlUX0wr6RpvF8mjslMzA6RAE0RssG1m2pSSdmuZBbFSUA7iqjvdLwdISYtMW3gbTJhEwecT/fUcRWaD9Uvl+UP4oHNehMql4l93goWNHPnM1sg8jY466P+fP6ZoW7PY9Xnnxj7iWRQuTCfINKtt8TGRShFsXQLEfdOW/iCBAZACxTE/lMuqV5Y0zxsp9gS0GXHeHLADWHWuxdzj09ShP9QPfb+2uES7bD9lxN4oNH/A8ZgrVJcWGAHKSVxlUADq+M18i8oanGBx3oRPYNlsCTnwVdC2SCC01mVfs3OCOyO+gnrUrRnN7bZj1VxspOhGhwp3mC4tMz+ZxMWLHgzoQ1yVFBGsgiIp6qWFt9U9uhxSkQmDz6ZGOSpXjZmZkaaw4Y8Av4hf6PCFtafj9MAkBJHJpoBum5/J0U5rh09WxhqbbuacqYH3yn8iPuneAb+d8E4Zq0Y3NqOd64guaSVn9BSK0BGp3QmhpGuWRxi+6r/I/2/IFE+p79oTohEamFbWmj7IN8ROynuCOnynzZqcCChqQvL6U5asl71wddP2bwflnpwa4jmHgOt78tE1DP7tIVx4lwWKcLn22Z9AuF0zovryQe46rcQEmYIEx4lBovUYiJw8tJDDlkjiOCgQE5HR42YjmP3CZh2MlShb1JmHlh5n8ZoxtQB2+IcMPXw1yFWZRGqvkNYSjN6jo4a/t7Rcz5VkKJp42AYN+1HxVNFkeC/ghtpZIcRPnD93OID5RsppUQf3oeFDeVqPIV35XdJx5ua/OCuYCJgBmC2rMQqEazrn8JnVKl/suG5o5CFoPbwYhpCcwE44sV4IxnCWstHgl6QMQwNV5D7TCgepL/TY6djqsFmEwYRFPAeAUs0oe2IGyW2L12cRFIW+ALrFwbj6dpN6+3qoOLLFMDfxe+a3KoJt4Dq/+OeziGgLZxmGEqycRpGhOxXtwWl4hSFA9ULymkL1k9OtnnaiP1ptI2Md1KfX0wGDlGOmvKt7RHRDFnTXFw/GHJEVDvHoCUX99huJ9fGEgPVZzv56AoG6PaPr0B9rfaei/CbapR/YhIk8oxQtPxClg5MnUHadoDKoBlnTNgpwxW5aeEvAeywUwEMA+8Yo40+TnNu1ABLN/iTT3g9huGpFmYAzYQJ34seYdXnQjj3Tf8Jm/V48Kbytwgz9EuS9VEBiL8LVGN9HZ+Sqk4qkuWvi3kHvTLQL1KK+PMmEt9S0PBwdFlKCpswapEFu85Miolzjpnn21f0KXEpKT6jA41K+CO30l8jr6+xIlaaCgxgy5eo6P+w2aWzP8G13AoLu5MCGCj07Eh63hQxQXIDQAGGRnPLg2PsTs5OCRzea+x/GalZaXqVjlAkYx/s/Ze34BTziZCtP7ifE8ASUQ5bevJ8rFcXItCQMS1aVxy9XhuBaugV3hoQBomchChUq84DJ32/r/3rSvdvxwz2x59L3WZiq4tzGf0nXav+ZCFOKbYgVX9Jr1pADD/O8CLBOf7hnC8ALvvpeQzSDpsW17anzk7/53ngL33nByBkj/zfqU816Hgm5X6bYZeLexaGDGHtHIEw/ywt2ybutDz24bdO0EgXSC71wl3aOcl2jo1ZVHQX8uzZv2H+5BJEM60jmjgDnZ9x/MP1qCYZIhuZITAfBVMRz1US6Y1l3fUwdOvAsVAPUPTC3rasx2PtOVuZxeS2P5JDPZOTDH+r8Fl5mtOt0U5ucUOUtuYjAOcth+dEjS1pwdnOiT/BCIzUFVvqi+UVAQ6aMJ6DWZzwHMSIkni4cJ/9qwuSo5uCi4px9+gybl90/oG14LV/ut/4QRzgGTBPT6R+vQkYvgTzXsg1EIAPS+Dsiw+x9PmblzDpX+THm4iXjirD3l5D91AKo39OcGvFaVlgXcojAx7/1v8gQdFNVwn2eHb/bx6D+hKk1bjKHLFYKnDPyARhkHk10O6TvmPAlJ9BPHvIQxZKCLgmOIUq2Sg6fu7cjjKkFGX+6yK1QpRkYavkAtYIUbzdmTpLwENfW2RixgfhMrOtq1fatjB1nhlT4QsR8iekpRheiZGi46HNkfQve9qWzbq95c0Z6iBN8UqpWprgmQvfpkS4mAehY0xL0MajIv/pyRYA3hlCW89YeHLDAvGarInNzc0ZySX5oLm/W8Owcmb69WcoWm9yEVa4++/yghmT09ZniqqeK2iKLpuvx1qWFo4+weWDkeiSAEmP2iy+rSgICgCmpQXa9AEDkuPJOq9mD2vJPIpqMq5FsSLVTeacQxD9TWAZcGkglKfh57O6W+FhwLU7eyw4TJtbS/10TFWXhRXOW/XPqGdYHRLAaVV2/iLKeKuN6hzstlD7g/ApQFQYh9qgTtzIy92jylfTomdBu00wtOzXSmUAAPXIH2FUScPPqRnLmJaU+5jxWwLrIaWYip4ZtxvF2uALENAo+8LvhSZxf3hPN0uTBM2f85GODQ92/ULGXFfOjX657zoEZ+5/uWpxegtQJpwX+R18C00TLUZw+gZBPZsQbWIAhM8Uv5spKd+FtOk5xh7ldFQi4xUYOHwXvCz82Uid3hUfBr9vl5gv0zbypfy5HatG0iKSniY0ErLTx0JR2zM4bUZqHDXLrSq1ndibOPEt4osCGUuAf13yVTgi5qtZTKxlAaejVE2vtKPzKZgI+sBvBX4rw39HxOKhSLvTnSPenME7xobQKGaA3li4bL47TEzZOE1TNWbTbN/a3hwIed80rELOzAs7fYmEC5CQQ1a1nDKzEd3/QiIczhH/yRbJnZdUJ2iegiMJfG0Y4p37p+5qtDINt5mdml80BqGZpnqmM74HAMa18oCEVC316F6Ulwt6Hu90T7zcbLimsShEBAlS1ed2krUTrLBW5r5ettFGfTJAGmUlGyvS5yFic4rf4O/eGBpA7M/iEeYfW5svz5seA3w7yK+SymOYIlU1tPDHuZwmvKKaNrv4bdbQllK678cxq8qDP8aZFOqRHka2HULbGia9trdZ5lZLNX8MY/szKG/vMNHcueVSqFvInPjcehvi3W3gexleaMzPIXI0mzMxv/hbkyROD9jgwV0cK1xNoFBPjLcgcI5Q2pkizBvW7yAtBdAvqtxxSjHXPFMlAYzTqSXHDmiUCISwzLsFsApsOxB200osvbbmQel+AdxXQhTVzH6MHmGkXLLTrFQcPxO8UTv3cIzP0cymnYhBBv1pFqpABMMCMA7TJ0N2hlutAyuPmwjs5wW7L0FeV43SRkaE2Z39QY1rEDGFB1xXNwOq2vZL11LN2laZT87Os0pKZsKTp6ukfv3WwgjniJdWA4aXwhPctO2GmqVtA64VZitdIViw7LZ99C9Bs/7x3LyFFjYz8HWsFvXCdXWVsu1PrUbOqGfd29gt8Qou+cR+okJGKupCciNvBpyw+HUCIgF/TpDGWXd4c26GmkGgOlZQVhHp9ZxhkQUFwIRWehHmZbdxyMsH7mbOy4OD5Zo9Tbykavxmz1lrMnKQ/M2QIMWYPYd7Z3GXvdzMmUKSGJHf1pcrLoZNvAPI1FIXgH3ROrfPAd1GhN6ZCUZ52vzpfMAL2nJ7jDfcwcyYo0Hp8l9eNVMnh9nnyNyI1kuiwsAl5WzhsEbrHCVgnRYbJSDwB1yQKb2hPS1vlSHNT20kKgHKneb6EZjPPXYMYPf531i2Pc9mP5rQfzcquSeWyyLLRCPB8KyYiO/CIhi7OA+Sco2gbthpgMXxcMWhpkhRKDf/uoG3t3wj5EAOyO7cFB7FW1PXE9TWjmd+eW/mNk6C35A/pAMIgbk+ZVGIkmY+Dk5G+K+QFRKWeE+OWvuL/24dJSpCiJcPw1Ecl2mtMYPAmrPXzKNcAB9J6ykln52xpLwHkaaTdKaLZ00Q+yXnJGAbDpisicZiJjvuaG/+6ER2ODg9wIlU0gxOfPDQErKlX2Rus6YYlglwl8CLWsWoWp21Y/pZBJzk9fL9iq7k7b8KvbzAPXiLhTXDBVFASe29xAPt0bS3R2UbfvOhS/pa1z2KpCLMXumRkhUxijBcQ+Hq4MDY1SCIGE58y9dq5t8R/drLVaqgdLdW6dd1mqn5EXwPgznESG0w8HailW4S+loULtD8Cs6tcduzVF3qJpRb+cpaBZK+ECqufVxtyTyoMedIW8+b8mQrvTn+rAwGhVm96HPoreQdx6lmtk0OzVqiGCRjhLiK6wwutRO6Iva3inBQCYCZGRq1zqAfII9ShO39OLgOxKrWcImeCWqpjiWJ7l4ErHwA1Ht8UhfBdJi8LfeHho740QqQQCY/6B5r9mjX5KT98t+Znn0EBkxe9sB3pHIfkAR5uSindfUNWvqP1/KgPqM8H3VjT8BI2SccPZndDhqkkl47yZi3s0YYw4YQvZ3LiY3nEdQN1z4BDieBuVwgUdqSd8YKQT7x0XhoI+r+PWm3hia9aP+Y8SKf1PAxvhKFwJ0mx9eImLWep28RJOrC70gEpkHicDSmeJA9mmevC3p7j/JPZrGNY1M7AoRPc+OwYzfP8t5O612EbPZ9UrLDAIcZLbGhy6VtqTHJ3B7kpwgniPZY5ost7Tx9ZZNiFI9d5r9kFMN9nSBB+Pu+45ZNQf2IvIReLvpNwOAEb76bfDXDoFcMkD88VibqUCyL9tG3AZrdWoiLaY0o0LSezpepaXmyANTJkpcpB6xpWIqRtbTVFwx7d3/j4ErV0v+CtehtF8ddmmSkgeJGgQ2GAZ1A5Hcs4K+Cm0Gcm9DbWEv9eaeuKyIvaAGwaBfSsoSeFx0F+qA9p8V3dmNu4vISpJ51JEB/pE4mvZdAyb0rvMjwtcIJ4JVurvpyRdRiQDACWpZ0tEDcGl+On50I4dNwcWX+wpWfIy4mhhWjl0pLUCaOKOSUGLfL3ue99x4h5l3U3CLs3lEigWaoOcM5M7MrNMnOXY5zcKkWCKlBL06SWGe6Xkk5wTT8g2adI7DC+y1MkS1FVsU3W9WehDMqWNYrglOQWLzNOmXaJR3dc/fA51YHpaRhewxlmD0n6K8MqZ8eqUxthReA6O/5MNMZed/Dx0BelU24CQGRj3OzJD5ZwQ6tekwbL1b/B0BNx1QvElMqZ2ryvKO+UgTVicXZT6oIH5sSECOAZr9od4cafGod+orKN4LWcdacGf4Fm5/g8RDuxbU3MMDtj8/p3ZAvAhaUzD5ZF0rZ/xJKcYlAc5M7n7a+IKU7u6UYPgi6G1SD5oVfnvtXrjFPqSnZtB+yn/N9hSwQHXXsCp1YNJanwdc7hNXTnOf2uSvadPC+AL6U8foa4QbP6h/uCiICmkTBIcxuYg2xc3Y64kfC0w+N8VqOQ4cb87gaJtEWCM3EZI0UOi5UsMY3M+b7BDsjRVeVV8NqMrllw01IZrL82epyKB5H3VgDEEGSzWZOs+phyr453O8q4WtRpkm4JMLgF/DvsRQSKVAr6BPZZy2gq+IDC8MjAoM4h1BCFf4W/dFQwqQxhf8bSb2k9vx2Q5Dc+Je7Mm/4JWyfox6tfVvrTFLHBaistfs/manbFRr8G8+NamDkeGL8D0chEvjyBAR2Jg30++qqgjwjq2NQ54P1wYmeD9IBs7/TmQMCByXbwUorWaIsPxxOT2yIzYibBMVS/5p9ONk2mgs2Ud9gvvI3tn/uzqipF5hrbSssW/YTmNLxv0v8dFJV0JlW96D9x5IN1kXTdEUwSotzUmgKe6KEvCLSlJWLq82OQ8q+3bFqKiguIog/dt/3mPr6X2WPzCY2porVgEvFEsRcvED0bq7rPJ7R4zQye7NW6LJS6tZ75aouxfFd1ge5cIhFfQfaX9FpzpGDNbLOtJAxQTrS8eBwYtsxOyKK7IyeC1CMa2HG525k+ieUDAa3EBkyvu9bGdi1wCl/5y/OviFO3oFubdlTFypNDrVuIXdGO85guDk8jMNNB/SRGGbhwOIa0hvNclAwmWX+zkpm3X4Mzr/zCqiNdgKJk0IibiLWd3qKOH/3Nm3bDq2Bst7hrkjK4uc63drweWLA3ZjZj9Oi2Tr6uhdElbr4N+y6wrkTpsRG7RwD/Wc61b9jCCqkGYUddjkXDL7t54uh+u+WoHAFlPkSzXU5krx792w2qMAGHhna4bvHMKBQqTeegICKGBicPiMvgUEXPPd7yKdMe007+ptBwKA87iCzv3BHahrRa5uwKxhAu00+xcdNyQD+9+L6Ko2dBqcHXrniBKe92CkMD0kw+IH3FD51sXW4Ppaq+XvL59eGRR4I9ixH7igCNoVnYgwsaBpqs6mTP2drhFhK/FNrSZdLSskAp80oHdGcg9JiVDZICGw2u3DCw8CEAziuOizBU3vip24VFSe2XWnvSuC5SgbIyRKGNujUbgdr5TTP1kf3BWg2XUhpcBW2bFTdHWwOu8LlJZYZhRojK4L53CFNj6b/d+HHV7LnQ9etCTybZC3bD6cIiSryqBLOhqnwov7WPSYSBBnE+5EtPUs2pug0bxj5lOBI9y1QluWTCYNoZFSmqkhjqoSmvXulnSm5kmMIQ6ouTCHSmIpkpoG9WsFo8/5k/8s3p0ZwjHcY0Opi8nzy+EoJRU8Lc9/NzeseQLVNZp89IhPtK7f2ntSx0ItRq4kzip+ClX+xN/sth62jFmcvS9VCsMh8DkPWTbK3WBA3MZ7IQoEl5su8bJ2jn4FrJiZQspuO+xx51UGwsHWAXIOybAhOVRNIzbzCSIKHci046kOn/E/ySc+PUlbXgB9tjZuDR3DiLuJlDIeunB+Hm67LEXOiwIh5I7VEcODhEmJoLflJscbD0PqOKPToFG+xsdosXfXxGMPKDJEUraztZ/x654r+ljU2r8mBaHqhxeANmmRWSgiIpsuJHqFOkvE8KCL85TAqpDC/0t1+64mWASLODYoeaLgeJxLue+/38yPnL4fjv+69VgdR84m/E1uNAs53J/AWYiVTf1lEyOvRCcNPV59TLirIxYuFPsbbdR+7OhSx3uISSC+HuTWrwpN2uLlccRzdHf8NnwblMi3LGSoe4c0wdvGTsi0o9UBTNMUtXTKVS/Hfb1mTFxIEzdlf0ddtov3egoh+QaqwcDh6WL1iRoQmlF4XGzh/g8yryuEovcJFzJO46jERqQpCqa1PjdznkO5nvCM+SgqHM9GiwRKifo8Pv0qzlvUWKmZvr6xQS1npJszTR0/wKADo9yMDa2+kHaAwN5JntA7nvSfsAbBn4GxfOjjbR3Su/++FD2BYtmrhzMCZp7F6kGZ2alIxn7kZM8JmwlKMD0Tyte4yM1FfsB3L4VwkIQbV02kBiyKExH6RTejNX+qs1awu8XV8NM4saoIr1MJdXMJXVrw0HEHA0E2pOdtfvvvKpO78tsWzJS/t/4oN6G6laFFhtxwzQhL3rvA+qwflVQGDKALTFK7gMvwNj0Sx8+omo76y9HGvs2LOKkiu+IzGPzZXzv87//eOh1hk+Y1TfG0+kFI9a/aAx/GsWX7dhq8YH+sbocI0daX0h8EQA/AE2qI77KneETjUSt+6hNNc897f9jDBD65CQzG+B5pfaR2G/AxUFbvew7JG8T7gCWeB4dtK6iV59S+D0nNrLxmfbdjQ6gD5BVcfpeCavt9LtR8XIrbJeLmZPdWOXOUrf00MV/1ZfCMm8aKLu783EZz/Ehlwnj2TtGUPdd+/fE1P2RDvSvCm3XSoHp6JQmWXdV2uNsfSRB9QVAn+25pGxmGzC1dGUkj84Vf6nj7gPUaU3d3OA0GNC8EQU6kayzm9sxLBEN7sxoa0MI03BlXO4V0yrDscFdShAWUMOeDVff66BTYbtMdqOzmJzqlbB9jmVshBza0MBrsEDS2n6Mo3jZY2tLOp54VjsvSWshdNveMVK8QUa8OV9BNRe58mLjJ0631aHFmT6uasllRKHIn1mqpB/LpL1R/YTX3tTPaDc+rg5/GazElYD1kLAgN1c0zKIb9Uc1D7xIMsqga7PhvEiIr2t6YSi+dlN1tVESjp8iiESsIbW+Da/ugTizauYxxsm8Qj4vmYigUsxiJaaagI8R7IJDJb2DBprV9kvFn48EkgCn8TwKLVqYufoVDU0nBFdozaY4YM/F+GkCQkDKcBp62LDWFcIt64gqh+KWd+ghWG9iEkHAWFzB+fc0ZhK96+Sv29PeChFZZwYASOw8RE4gAbVl0GQhRc8k+zTzHwy+512wq5NVkCItWCIuQ+Hdd25Z3NUnUUep511qyVCCLHg0uKKf7uEgA6R+rN86AEd4IJCt04A9uc0+r55O22yCQbTET/k4ONLlb3N99cfAEgzxdT8xT6v2GUn8iQtcdosGrGLsa9ECouEbHI4xmkEJKbx1niSlAPRXz4Kpf8caVMJuuimQFFYKfwvwspeEa5Lb3lYzjgM8FJYjd15QfwV/a63F+Y8MQo4ai3Gr71TbFLpxznRlyv6UN8Vyz6nbCe4aFyTpXeEBpfPuag0km3T2WHjUT3G99qe9S3lhdXqqSr7KiR7i5kLabeXaY1NVrq5TlYvmFbQTLwgArEJXheWMz8HsKZXLDAHb0j471qqov9b0srKS0i6SSjKy5UwecPAYfh+75uo2p3Qr2FM4OPW+vF3V4KB9/j4gYXvUn9QVStSHmuHZV7wPwJbq2OwzILWBZxzFqP79PNrLVfNfRZwcST6q4tmkstmDxtr6T3yU41w8SQSxeZESO90oWE1wTxVCNzBfrW7rBxytPJoQAVlMe0KvwseaOwYnW35LVtpVPqV15LGgwUJHrXbf6wDnvBo0cRJQE052YWvmMC3IzK9x2QoBMojhJDQNhiwjSYhIqi+tVqlzzWln2+YobwBGptit2NfZY3VLYPD3uFFKyBPUuAMVysIFDkl244B5gIh9XvmrDKPSr8T5CHk82lEfc8isrgEJVznKeclfyrXrKcBa1/OAoX+EIGEncj/hI3t0EzdElQFq6DNGTS9tqEzaIwci+SP/QHqKq05V8c8VYV5h9iXYAyeKLysxtl2LgTrTWhNBgWmO1yc58ker/SX/DOLhRXC2hEZj60M4+ZW1P8BFE1M7n0//4pR9CQHKfrvrHblOFMfHwxC4MmXifxKEXkuN+f35GyZlTfQt2jE0QV9Wlmmxuu7gbsHSzgCmP07EmOY8DyEUL9FnN9dT89FGqIfDCKJa5GFcN+D+hea+KZv0I2lLDN/zCX+JDkaYhnckJosSh8JeUVdFS3FX6SL9y8clLG/upFKVNECk9twR8tQK/EV2ShswWwwIC5jidKtXuS23owcdo5NFwfw0mlCxmYiSMNALpRrXqYnYVNzxabEkrzn1UspgZKH3jlmzT8HTyqZ+PDRakN8A3W6a2UPihE0R7psmy0u+142VICMA65BOEsqG+srYxTbzJpyenExdC1nqvIMUUL5QOvMvxas7VVZAlcB4hqYyCjyB448DUUjsOKAyboY0K7DVvz2gUpFMCvXTXI3Q0BdS57Wr+XuXXdeTOIDxxXmGlg2gDjXS2ETLJVIujrllIf9EHdNLYfa0vEbpeE4mceBGvfj6LdlcjcLhfezyw+WF2NnHeWHZa1brTpeEninZJ4/fxyjPm1Th8c+GVS8lafpNdhRaoRDEZU3pQl7U+rOL4dJRXdrBwBhhh8I1wkecGjc5aTmjjn91KndhXc4FBZXM21BsEDSxI5T4fOcT7kJ8uGGoFekjqSayTJDvWkRRVwphu4fXXnm3R2Ub+oYaey3hZJXYbScoQqwBQvH/wLguSA70X+9uiSmdU6mvQwztHczkPV9NK7CtlLZfp/OrlXxVyW/lyWwgqFdWsrLLxkZgA87MijerRKECYGjZtsaM4yNUjMnPoppGyc3nsSJga+SS1PtwtzIenQESIBqcN41afSB27HxhvVtlHHt/TRGK8TwaIturc2wfHabML4wn86c+YA2293jF0WbGXosiNJN9Y4KqjgYJB7nYycD9bbGxa5HCW3SU+uQnkbqTOX1+RhwNmmXGK5DaNUxGpOd2TH0DWPzOSFlBXrnq8sHNJnhQksulkF4kLAm5OYhhc6YTGGZa++Pdx6NuXXMLeoUHBdpvoO6zDI7AxABOWlsUEyKgWdNXImBgv+7arbpcqGeFi24u3JabKq9eqPWJt+7qSXClfd527oQK1q/STqcFgtiKu/KQCw1aQhWOj2EHk9Lg2ZgGy/V7ISzAeR48I6ZUB2tZaiWWOZss3K/KFXOHA0IiL0a5tAkOEgkspgI5JjRGik/e2LhV0XI2aWnJbSX1CTuEiDCADX4vl3V8MZZnUwSsiVWBRkBMQy+X0vJulipMo89W7sIrrWA7PMytIlQzB9UVDUNBrldc3E8/1N6HOh4p4SJnODhbPWU34OvfTMRPKDA8C3MPHpzSxVU7hlA0EiSVH9VHrvc6i5RvnNcVuYwmaYGApqicgZD0B7EQmCfyXYImq3iUG1j97nHn8hpiDElQel2GWGF4TwqS1Sf/gajt3UPbimqrRJDOKXaGcM9Sw/5KGeWoiDt423oLQH7ECRpWvOh9FkK3aEYEnVPiBEd47TGkNv6rKASypVwlSa4feYU/Dlfx9347wUoTxz1IlhCVeJvog5POaG0SyazXa3ZMjLyeppm/1NGfuowuHhtjC9pCE7V4zPMcL5dlGsxLvSOBZ1t3Aypa3oqkULpNnNZRAx7pIaK/m1o4Ygw0xsNnl2mymEDSJloHiAxzT3HDE6T8fBB5tX/eKPFn03yjw10RXK6Lf74JS0aSBr63QXYuR9kb27TBdbHvmLxb11y/ZkVYnchnrvC3QUSRNhdbZqx5iys0b9iBd+B0b94XFsNryG5R1liRcfRxtWOh6Lbm935eS5mFAoB2qo+sJKDVJ7dR+J+/tjxwsW8jMg2h6PVhO8p4IXk19/BIBdZ1AcI6SsENHoedlJRkFG987/JwuEl6Z+88TPOAdEDhobSHuld5UU94uGp5xEMrQNTyZbiS/g1feU/aLYR5Z5eX9k0jg0D6GEvC4eQuzgiQ7/kGpDTz5AGmHLNkFtZB8YMuBHAFztj3I1c0cRD4JivKZ4WAlT61PVBajA7pdrx7MKdsx442vlJdnlAL4ov0nFlFnKJ6bd4OXHbkUSKGZNwtjnNIw3y9o59CGaRHLHYwhbW8lspjmurV2JUaZWObcpm0fMZfXdsxR+hRjASjLhiQ7wdPhzsAktOsUM5qvJdkXfsJf5iN9FAItFh1pieCZDRXqrE1KCNZQcr1suRRf9Nod5w/9tf+to+v6iV1IxnNbiWCzQq4AejOWby1JTBKjQKE4Q2PUO0UE/4sVqgRJFJJwQu+KOjVT6sQlz+qB5v66TrFLIOPPjb/VeA9u8qMPqGwnhOn+51dI8lo/MOvGF4uo3qN1ZPShlawbH+d7VWpjrUgodNLM/UW90AEAdMk9y16ELW2WJTt5wXYCqjtmCyRyYegQSQm0lQiCPqTg2h4TdAB/uuGPIH8id1VrtKC1D00JnzDb3E9ngNkYnDMRyqycgvK2/ZwaHN8ew8djDuCd96TRqJ7WXlzl7i/U/BaCKzKdSm8z6lE1o/m35BQBST30q39GQ9F1+tt23puce7jmGomqmHPLZ7SCUkEVcYjaa05F+UL/XwYaIlkb19eg+Vkp+WanZzBr1/u3c4MsGc4RWOV8LDPI5OaHBs66IACogah00Rk4FppkEUz+cBto7YoHJUx9thpgyPBpSZWMzaxYfQs0e9kLdlT74iTuMbbaKpWdac7+2vwJMWbH9bj30rX0x+LyPoDmx3ClwqQZ+08gnlIqKy7FPn92unhUlMO9b/dHxiRz2PaQgog64wTqsJAu/gDrWv8v9mCWEMzNEXSjOCa0j8uFE9CS0ye2CrTPUPKe+62yVAH2t6j6twzdk5KA6nFcSK/f7fTnDda1j9aT/gWhQtx3cqiKp1dYnCRwN/YKSKt00As/2aRyZLbP628tnN8pTNjD7Z5YxJLzyALcR8fnYKfZkP/0ZttGoAypMS8SGirJo1ObCL+AV71ddk1fjPAtWNL6N+qQZE5yOG0aFDsJI4Nnd8g4dUUi8xkVbKzMGSdkbprQexw6pwpjhFM2l/Cjr/cdMb8cs4kAHEfIflxvqKmWMxwahzv0rIKjhPArxcdWzWyQ/k439XeSTfg5ocw8eKZ3nJ91h8iqQDcqsiCTTMMC217Hxf1N1hb7M6JrfmRNFGFffY/pfZHZBQgIX+g7yUXgUXaV8vFR9jycwbWBaoanqmfs/2i+ZqDbSLYZOFxsYl3I1ky7u5MbWZmrR7tcltZkJmQfXkbzX2lncUpKDcfckE+9RK/6BkczVzjeh5poQlGnpg0w1n6TvSKxYoN83EvdAinOMp8GXZzz6s/KZzaB97I8Yf04tpEKR5haxUiJmYOTGpwdBxnHIsQc3RPEIxn4PpiPj6gABDaNk1bNUISMVTRcBrp1HyejZEYOEZFqdQiH5FnNG7lybVsuUp5D7hutz3ZK60i6p1o/BRBzsAHwfMTP2cnIx88ok64EgVF+CX7dWLfS56lzLGvJLPhgE3mfTQPtwvMhZyZC00jmrLxgkqknSkTKOdd9p1QH2gekiKdG1JbO/DmWajoA5/kOkyYfRbybs5+7Zlek3fOwi/FzBY68XMpTt5exql0ZXJswm0gCev4Lu5WKExYWYPkPdgI9JCd9zq3kJIjKYQP2VzdoiTrqdmpA0tN8izLG+iPhcSIE2sRPhDFBRx59fiaGG5m1fenwq+1pQPERZobh/+wM9plKRVWlWyuiDHOr4C06HWPTMmiYwF/hKS3M/r81B/B8eGYTXKK0IwSEZrg3rtBlbhIIBPwJW/GoOOUBZzlaPyJ1WLVHWdcmFAZCWKZ0ZQKi6M0fFPhzbPMxr7SOatDeXBj4pY1cJY2EaRQHwindPcxL5I8Wiu/2MgUGh9CGXttImpzzYsAgE4Nu0skliomTtQ56uIuAGgiys8HJYj4OS9i3vGsV8DTTcN1KdKh8oGLGF0zwGiMq2svTrj9b+EAHvkWYwCN7zdMH433O9Nz/LJsrTIYOeTeQ3hk8z4A5HDDSgtbFuEoFE56w/7bL2cjWEYI1clmOpPl6+caOBQCQ5nYBzggwH6C3Fqu6Gf5wIzpRyVhQbBfk8VaKZ3QVA/ns7OHy9VqG0twxIwF7dxgLkIXjY+W/qDhe4MgdMyWoUL7vrG0GYMIJPC//6tR6rOtSYpyo4rzrvJxPbvhfnv3Udb4CF1hTVucDbt7uQfTOm7kFa5H2otnusTNBvfctTRwmjCfqxie9ubyqrsZZBABDE4WKEvguQl81YfBiCMsonWnacLVNd2QeKaDpAASe08VcMwW8ZmNomhbMsFXvRQjaLVD87ddinPzEUmo3lqMBas/313TZ9WbS8fk/NFJxLcp5B5XApYMiTysuG3Bkhx0byE7wrPUvC9lfS8inbrKcCsygkFmdHLCEuZqZEp64w+lMfIMuH2wAPfKv+dX4dcpkvK3glhxopFI+FlGBRKY9q9lj9BoCZrl82l8vCmoW7hgFw911fSp2Fm0a8OrE36RcRqFJVXSV1441L8USS/cKB17wBoSFu/zuww2+kKH69KuxvEfeF0l19r6amyIhwsg3dlwQA2SsntPqBfhzpevKNP5dY31JZbbSUwbUtFkGHNB6YdwnRylUJ8PXIEuusO8UXNR8bM1dxwMMXhiYBYlgRkeyQ8Xy5OpIDv8lYJtUUIXBGMfL4/bJvPkjip4cftxr8FG6TeHwWsE0+rmBx5X+3Ql7a+9jArDVmerBir+0wgc+rslJZ2XWn6Y82ycQxUWVRu7oSL+uYVBayAar8WTuI+9wGsvptCQDN8FfYO4JcY/rlThfVW80tlDUraOF8K7AlPJE4e6eKzp0QYRH5Ntpp73NO48CGuniI1LCKR5xOz1iwzKr2wutYvAh1UnpdVvU3jpnOo2kps87AYf8fm3zCX32+4PMmqngBOl5/fqy+pqDzVJNI+75LWsLE7lYR+P8xdGvycKNTRfsipeaUZRSKbAo1eocQSuu9s6kMmeeuCOaQ/VinAFUd8lMaKOG8U+LrlI9XBuZuo/sxyGzNmB/r0rrJJNlScxn0x6IbBRyk5FveYqyscrtdbMxWFUow1J21wpKCEcicBBDKvrsiJhXry7F0RVoISf7AJxDI4iimDhVhPwhpJEDbMj/6gy8Q+OD9eeJYqC3nZj1dRUUAspU/LyalaLyNfTrkR8nd1fqWk/kAJ9Av6+IFOjPHqyorMSyDpEs7sZYGeLCXBheoBKbuVUckjyCDUYePER+KrvEOmNjIXlMFiutVSEyYL6GlVX2pL5HlPkxDDN6P+UkvBUSbPhrtENSGCbJF9EF32nnFeGS8NwDZskz/gUcQZwHGKfXNUi2JtkwdXVLSm3tOCfFB+ARxI2vc9lr/yyq7HH6f8vbDS0nyJnmUwB5xYlBnd9P+iK7TjJXqy/EbpjXjMYqA+opKM8Ef4DdTncciv5Bca98YnbPCvYuqiyIwtKGALzK7UcP5rjVP10UZXTx+ecQ0Oi6W/TJcigQTtPyWUsYMPjqR+9oxDcxYAHX3SPEskzmbBRrTFwU+Ch+kGHYftB7huyX1e09ZF2/VPk6tTP13oHKJXmXkgyiF9DRKHVpiXa4IHWBkQrjoE3Q5vx+RzRht3ZebwIvP6wyUF/HuxDPIP5TaAGFZJOeFZX5sygZfTBp89xhB1GYWWWQ+7giFh0bd0bMERIqr0QLiuFfNv77Lq1dDj+bNt81JiwAyrzftQQdUiQqgJ9KR0rUCH2H1CuuU6o2f5eFmlZYT0yHmbSWKOzlqEq5jy0+AF2uPFLfZ39cIiZUHw5Yzhusbn3thBJazXSnqklCZAR6FT9EmsrzHotPenzC0SIV9z+7W8ebBab59abY6qv5UH3L1EhEQq9YMi7Hd5XpFdQuY52ONnsy8hFm4AxQDQAlYBuElp4V+1XTvLYetvQqAs/mLhVPK+Ti8RQTBnsgEkABHTQCcJlIVyARQ6FxpwLcHw6ba0ZO5JW9CYZ/PeSDkXs/rwrcxUJ2P0T6D6FCf/kJLRLGJ5+pNdNpFW6zCPOV2MgEOrvLGojDsM2UDHSd6VAkCRQCaZuy9PT2/VieZzKI5WjHW+KUeah/zOFpJ4QaO/eIrllpYb3Zzlw6bPTqRnh8DVzr3rbMNAnhyMoykmI8/b9o2AeTRpJxmVNOZvghX+d9QkBjVKVB1qEglWpBbFSDX0tfHtToE+9e6rW1r+sQcWTRNTI4a1cVO+5u5x8761Ofl0lZBBpXNWaRzZbbTFVK+wPpI14v+TK+5V1yJd5NoRTVeftWhHdSMXCcFC0zRGzPylCqhZFN7SIPJwazw/rkov3+HGcaGAvX8qhRwkq78nZFnrdl6Y6vZJ01JKNiRmTOcsF0sjxvLl9BBUAOYAIeBRuA2FXk5PKG6zHyDRpGGGANDU6vYjV8ebjFyNfLhXx1JhbWmvmcU+1rA8FC9XccwgW1yX6Ni1gd3S9Mv7nvRLvB4wgImRu1n7SIK9pRWILFNeMF2A1fnXAxinZWfR1ycswX5b3EVlDJpUhgnUo0luDNF+5XcuXgahXQeAqYVUP8tC7ja4ohTl+dI+xPgbomSDFzpqatD7a5aK/zAT8gB3XzWUNzVpQk2aROdwf+t0ZDqFjuWQoNEbLKaL4ImKd26m5wm1o0COHE4GBKuTNM8TZNAdg4GdRKHB2sUwM8A33pfsYR+SaD5uLFys4jyqJWzQojmr66XbFgDQwIYAvzmmbPXjwcVxz2sObQjHxpW4PpO6m8HPFuUaIdeKbVPIsRAZ/p/1hAaKEI2fcRyhjuf2uhpTR/0T8m9v3UkOG6uxXy4hRVSTJ3rcNPsrcCV/QWWnFu8V0MOSUOPVDnNtbWHDpIdG3w2LR575h6H0K0bo1ofkuUkUqizMiX90O57IJuHndNlLEedvLZGJkobj9Syt6Os+oeFsY7DBnDm8cY0T/5d03ETU/0q45FIzih3ZdWHIMGiMF78fL4lMRFxb9aFGVcbjQvvtPlj66uCoYQ7hvVnnZeIOZESObnLc0fimEEbmI6rPTWhkI+dLc8K/5ucBobP066MzmdUTIT/bBcPWY6IBOkefMq1y7N7K2pm7385/C6ZxHTPKj2UMsrqOHMTZzJEE6ScVddBaAkptUGuFzQ1WfVF3jQbxKJHytfeTlpJ64FpCbe3cCb98UyULREt4vk1vBynsMvv9I/M69coqUrl41ECdGTUNgoPrea+G7fjxx6IgkrEZf26N2DDfFhun1nT/Qdjxq5SUFzHnlWlbYrhY8peulGJTsXEPJgWiHDoNWqwW9X5VYpp8GKI3yGzPdC7LTt4UPQ/QvH+ckSNqMNIOkKJADYkilK503nETkl9YrxTM4WVA9Q1oFJAivFevetR3pruqKz+L17oEtxBZKZqRtWwLxc7CWQ+kgwige4vfF3aZsRRPI9E1j5PQ8TOHfquEah/LcH0bMDSflB2fcCa+n33qB5d+/FjR+ahFGrvhm/KYgkCxnrvwJ3ZMBDQ5RGoItTC5nPW74gWA/bSujg1xj++j1SaXzOfGUVq9OSbbNR0GYqaVUrPcBN2bN03G/50CdUOhsHj83aQcyHIfg4zLv5/cRi5KqqF8jFO7j6uYwMUCJYzDefXXzkCgL/RiZccrdZpCS2vfmDV/E8Iepg3rslnGr33t5NXCeytIq3w75f1Ak3/SIkqUURXErCPlZPg6Gne8U1aa5qmo1A+RpHSQTcBodzCpUNb6P4hvSXg+Ax4mMBEzBQMPoUeC0biG5zxgI8+hz/rVmbj9wo/ijKIhfnlwkugpz+klUgnTgmh7FfOt3L2N3CDuDucgnK9aFAW3lxWa205o5Z3+jFAR1oH6rL3FV7YJhjRCKtS6r6LhjLI4JxyRdRiaH3PaXAMkjafMD/NLyX/VZ6gtDlg5Jecv9sST+m59l79VwwdqsyJ9m+khrKcWrtYpUeDoA6VcYisOrWDxaoGGVEn2VTQ+EDfYRvQzk/rCvzCh1ePCGkOVg3h2GA49b2zpnaxtZJ5WAWwbnLyX0MXQ5hkiOiFXKXmXWrPzbTOlls35q8SVIvG3eF3HE16c6+LjatVwR33u5yGDtuNGw3JezAWcaMNhgn0xlOoiymfMs70feRDUSsCWWFTWWdWTh/wAVqCUdLFV704Zu8VcDUNvX7kmWcrdmxfnkmnqHeKQK6WBCZj8x/VOAy/Ntsf6v8o6mB8QkgTdbFuxMwh2Wsz4qbI8ikAwK21VcS59ufN9CRMTt5TkmVQEjyU4i6Hh8w0C9UO/x40ZPFhwhjBde13+SdEXSNoGxcaGpMII28/uO3wXZNUKJp0FJOUh61ZqB1upcZLk2u1YJqUWS5s0qhVrSlBqj4p7POFzVKQfdHNztOzmkYZuWdUNz2rXYl45H2NNQWUIK0zmmd6W65cUKa3FwVroyf+GD5GPqqpr82Vbxf5Y+zWeLyegjQc3s4Sw/f5zSq0hfBvV154hP6+6PkBdnVC/lvE1xeCTp3976tCiDhd58sreKaY03kLZJhnnvecfWRwQYCP+UzzA2126klYiA89aL/o6f/+0A+i4SwdUNcnrwdSRRg8KaDbQS6zWUZDu0k/O/VXqpiW4Irsa3uN4bzl+CL1O4a1sAhUMo5h+le8SLlVTWT1abIOFau86o937DBrv2XleY62N0HsqjvVSlFop2uEKR77FsTpyUZ2TFwIJlSi9cpFgmBfxey99hqvGrCf3U25wDO5pnAZ5l/mJcD4Ype3PFJcCAXFd6f1NapkVErg/o4N12WU2RHNNKUDsUC37r1xBzzMYrAX5U5xgXEItRXP1LCDC/dkf/spFrDqDtDnVOetGtjZO6sRKAdH7HeRRL2vsYqKy8uH60oOmcg6HIPwIQeJwUiYqBHbOOLkt11o3ps40de3+3J3ng3aU9CjUwXBDJX8nBMJ4smPipwfkpbq0Lr+CgOwrMrIgVowYHQOpRUZhxJHYC7njM5HUm4ittG+AZLYexyac2vYSwiey+2zR9xYaxhFmiCJdtB6gIcHv3hg1ModmO6yTi5qsd9K0tWVw/S0znknnFtNkarzSp6fCbSDOqnL8ns1gd/0Vrtkm8CqcYQH49iKz3m64fBMu/BXQCmGBIVzY5L2EDEVxIIaghWrnBpY6dDB4CxN8nzpONzfEDbreONJiEN3DjCKm+2qbFt8xoFrDrW0C9PGC8oHh44iV6DiBBVeMnylXE90Q9KDs+WVr0xAIn7NwKmrL/GjVwdI9bRSmd6OrA7bB92MfbbWEOq/pBr2m/1B1oS0ZQillPpA0gZfBvg+COYCBPuZ8rg7SW7yTu/7QWbilzLoZdz2m/mEAzJqh69jynGVNWGG5HXVoVNw835tRHYuA/e0I+UikDfXPkcW1Tola6buXb3RfUpxCYoZac978hiRmNYn7f+gpmOoWGbiR/XM8WZePkz3oDExuKte/YS5qixJ4VtyDG+Y1pwzALLdlUDLwYYnfxXMX9WPty/mB/rZ/2XSoQZ3BGVlyAAaXQ6uRCNpJGQc2q6af/Qj9j8w2GhHndHQs8lnbnf0922TjWL3YwQ4pu91YdC/6qL/weMYCypJUaPhRBlsZjzWliP+KgEzcBb9MaFtgQXXxFWvUoMruLCFFZ/uRk/u9rzXLh7gKSUxZoZWJ4se/jhIYGh0qwBe5I8FL5SUrYSLOyno+1995CcjFDOxsWH6lKGg5gV6SiuFZV+AR1FWO7ro41vTiNrvZTe50b1ViWz/BJMiwb78whf+zxsvlkoromcUktywhSNk7eCdaN0/IXEpVYz5WDXUwH9SkW/8Dg3kSZA7YY6Kug4s1P5Y4QrsLb6oPsFwRTasivNoCdaBO1HQzv/T3Ycl588YkasSMZLHF9ZgbXz9qVdeGdPvePiefavfeEBP3JoFoy0a3tRNXau11LGlMGeONrwrZIqRcUCLerWX5XMhQ3E81wIHJxI/4FCbDX45eo2h8wDRUpCUwsZmLsP+DBP+t78cTkTk9yAHZIp0KlFocTKFoArUo9OyMzxMOrfgGoBRCocrrElWvCby060zhItDmyZehoKXuBj8ei8aaglkx6fo8wVdoAM3eXQoHW10PhoKPhJYD+pElV/niXo+JfR2pFLw+Gn0qnIhw5KdkYaaBBAW/Ub9OK+zg71ecrJvHB90acpjUECjzRYLHPk51fPbMs1uNu7kT12d72qmEW3TpRLyTDuqzpOmhoH4+yIUm4+qLj9HrH4YxxUi+2a7/DRIMusyGGOMpC/0ltxNqkIQFMOd1aKkwVHdJYpyymQ9W7ydnF8/PRJi1UD4fsljpmRAU44Y6XCIIUuMLHvRDhtx6qOA2oKBgIM6WBC78ganDm+jf+tNHh7+s2FDSSQ+2ywvFZ5ddDFxWb5R5TOUWbKyIHRtnFZLvekLqaSWEmSkn1CQxQj/8YLpdJQdaKxxd1j0PcYg8CWaE83V+JAj2bkdZvbaB0ffJCmLfkPUQpsgJgSKTLPuX2HXq0nQx+sfu9x4WpZIDNViaY6Zb+vxaPkKsqzmVd11ZThzGmU1FRTpJCBExtdRZBCSW3xWWjudmJcCUeDGTKNvsi+YDx2uEzUOFioyJ7xA5TSzYeZHnWAc1W5s/LGf4jsnVziwSTBipt3zBShMo8msTI9wgL0x3FGsIFzdKbTv57uZemoN8Mt4Dc36VwDe7BqeIXAvuvGAw61OVMxNapQ+B8Frz8io7ma6ep/GfXZd0jOb2TScP3ooCAee20JRGpYDQ1O2jICTQy/NLfw0d4g8hYpKgRHbI+VW3t7b/IXZqzo6NJ0if6UonYstCseKFI2j9E7zQXY2+QhvZZI0cUf6ReQKbdcPNEScigHm1JG4L+kWJIVXo+nhalCDQEYPr1TD+pMv86ylBlIKUodqC3Ooh7gjmqtpyUQfZDTBwYHH5SuzXV2gw5n/j3OxdYuDxSa7sojP5StoeqrTHJO+2/xmNpf5LhmEQiRQEubGZ19qJZPpZdcfznG+TyfDEEXtp3Z3fknbb8GOBZKZgw0h8/qxUaGle6a9dh7D6tltkBfLiKuUaEg+2wGjResF5VmTVZpMvB11AfnjkwLgl5TZhqdV2YEvA/mJxdvTt9rIGkv28SDCK1Zp4ruK8aTy5Cvth7wU7PlzZwSBr83qK8BUwtQYtV2b+UzZqy+7sIbMtj3BxIJq2ongHCpa37pDYAvUUk4QeKmY8IG4+7vbWpn2w6UhBJUSoqbKYNHjk+eaYa1h9YFKlGmjlt8Y1fEEFDKTV+BXKrTmfXDSmPUNRSh1UsUxtZuxw/zfB/JSOh2trteClWF4lkRkVyB88GsJvwNldLcmq+HMnzRVWtSd28kTGbLqmTky6oDYuRG9erx/PgThe2hxNfl9FHWwJLtiGhJiY/2jL5F0GJP8OXCiXFOOS83x6//5fwaNw8CXWG9BVjYQnIz3lNo1jKmJWAwSLvb1mGTIRF7qtCcBlddC58ny/9v1HwChcMvjGQD4idPpahzuueGHdjKkd5pHzK1i4Rc6QNbQJAk7ozYPPkq9U6svWYd1nenuHAfgxrx/CFgaBGTcFE4Gb6jHAo+jXBXH3oy195AfzD8lZ7ME6iI2Cv8+redEoM7t1pDDkKnfKyez3FldPhc4u9AN5uCI0tPasUL2/nlRDyZ8uvIvu7jtz18eznn/hUNiCpEJEmoBZf6TTslMCupGvnBGZJr7QgsUtA5bqDIIFUlDv3pDfxqQ/VyICeerFYkmVGPbOh8mYLhrNrVR5onpr1GdxiCdTdJA2sOG9ESlOfsiQwhDlQAH89c7L8VlvHCHaivKLLriiZhzqRAr74utRqi285svYwv6Y0abnIJEk+uq0ooM8g0SKYhjG3syRp6tBm2efsloEGBADfhXt5PiJm2HFHFZ/YQVYZipoM18AVWGsl1dhi5eH14TekZssVYcI99SixewXf0XW3rHJyU39U1/t+NYFsQqS4VyigeQOIe2PH+87Uw7zvSzQH8n5oqMLq/x2yQmdmeIq07qBD4h4a8UXNIQNMYKktokRQQ/0oS7grT9iDmN3S8Cf0s8ZFsi36mWtqMhYH6fcO/alzH9aAUOlelHQoDu91A0dBmk4F7UAY1wopq49pTaMNKgpyE7B8TrfkVKq5PV0VgEU7UVwB9aaDWN/wdQMkTFNVIsk1+mLgM/ismAHQeDM6KPWnv+agC7LavkHyzNoaWD/grstDFSYA4cRU3r2HjJhqAQC/lEqrs6pyWxFeO7s7/8rXPIx34JzwXPIYJBLTXxToF99BuvuwD99TrfNg3HumRmXN4DDIG/y1UtMBTMAw9rXtgNTy9kvUOvZ8ed3EOlcy5tAvgOo1gYw8xaUmxBXIhrIcXSHXSIHBtH/o6GccEqOII5WqCUayKbyUYiAOYeZwKzIC0vU0T/1O6njj6mprhw2aNZT2uyFfNDdi5tvU/EoOqgiUh1pJM0nR/LX9GZT4PMnZ9lf64ftH2GIapk3LtHwkra9vQudmEr3Bt7GLNwVVQ2aVUkklNOd13DQHfveyAzPTtRe6BY6a3CPfbmRceon5AgAAA";


    const css = [
      ".ns,.ns *{box-sizing:border-box}",
      ".ns{position:relative;width:100%;height:100%;min-height:0;overflow:hidden;background:#000;color:#e5f8ff;font-family:Inter,system-ui,\"Segoe UI\",sans-serif;user-select:none}",
      ".ns:focus{outline:none}",
      ".ns-sky{display:none}",
      ".ns-blast{position:absolute;inset:0;z-index:10;pointer-events:none;background:radial-gradient(circle at 60% 44%,rgba(255,255,255,.9),rgba(255,43,214,.25) 30%,transparent 60%);opacity:0}",
      ".ns-mid{position:relative;z-index:1;display:grid;grid-template-columns:460px minmax(0,1fr);height:100%;width:100%;min-height:0}",
      ".ns-sidebar{z-index:2;display:flex;flex-direction:column;gap:10px;padding:0 20px 12px 22px;min-height:0;overflow-y:auto;overflow-x:hidden;background:#000;border-right:1px solid #0278a5;box-shadow:5px 0 16px rgba(0,8,28,.7);scrollbar-width:thin;scrollbar-color:#15516a #000}",
      ".ns-brand-panel{flex:none;height:auto;background:#000;border:0;padding:0;margin:0}",
      ".ns-brand{display:flex;align-items:center;justify-content:center}",
      ".ns-logo{width:100%;max-width:416px;height:auto;aspect-ratio:4/3;object-fit:contain;display:block}",
      ".ns-top-row{display:grid;grid-template-columns:120px minmax(0,1fr);gap:8px;align-items:stretch}",
      ".ns-card{min-width:0;padding:10px 14px;border-radius:14px;background:linear-gradient(130deg,rgba(4,17,33,.97),rgba(3,8,21,.98));border:1px solid rgba(0,169,240,.56);box-shadow:0 0 15px rgba(0,192,255,.06),inset 0 1px rgba(255,255,255,.035)}",
      ".ns-card h2{margin:0 0 9px;font-size:14px;line-height:1;letter-spacing:.15em;color:#0fe9ff;text-transform:uppercase;font-weight:800}",
      ".ns-hold-card{display:flex;flex-direction:column;align-items:flex-start}",
      ".ns-hold-card .ns-mini{width:78px;height:78px}",
      ".ns-empty{display:none!important}",
      ".ns-next-card{border-color:rgba(160,49,243,.75)}",
      ".ns-next-card h2{color:#f561ff}",
      ".ns-next-card .ns-next-row{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:7px}",
      ".ns-mini{width:100%;height:auto;aspect-ratio:1;display:block;border-radius:9px;border:1px solid rgba(63,137,229,.35);background:#020612;image-rendering:auto}",
      ".ns-score-card{padding:4px 16px}",
      ".ns-score-card h2{display:none}",
      ".ns-score-card .ns-stat{display:flex;align-items:center;justify-content:space-between;padding:6px 3px;line-height:1.2;border-bottom:1px solid rgba(70,147,222,.28);color:#d5efff;font-weight:750;font-size:13px;letter-spacing:.04em;text-transform:uppercase}",
      ".ns-score-card .ns-stat:last-of-type{border-bottom:0}",
      ".ns-score-card .ns-stat b{font-size:22px;font-weight:850;color:#f2fbff;text-shadow:0 0 7px rgba(15,219,255,.6);font-variant-numeric:tabular-nums}",
      ".ns-score-card .ns-stat b.pop{color:#fff379}",
      ".ns-nextlevel,.ns-meter,.ns-banner,.ns-keys,.ns-board-top,.ns-board-foot,.ns-mobile-stats{display:none!important}",
      ".ns-now-playing{padding:12px 14px 9px;border-color:rgba(52,117,255,.7)}",
      ".ns-now-head{display:flex;align-items:center;justify-content:space-between;gap:10px}",
      ".ns-now-head strong{letter-spacing:.14em;font-size:13px;color:#fc60e4}",
      ".ns-bars{display:flex;gap:3px;align-items:flex-end;height:25px}",
      ".ns-bars i{width:4px;background:#149dff;box-shadow:0 0 6px #00aaff;border-radius:2px}",
      ".ns-songname{display:flex;justify-content:space-between;align-items:center;gap:8px;font-weight:700;font-size:15px;color:white;padding:3px 0 10px}",
      ".ns-volume-row{display:grid;grid-template-columns:27px 1fr 42px;gap:10px;align-items:center;padding-bottom:10px}",
      ".ns-sound-icon{font-size:21px;line-height:1}",
      ".ns-slider{width:100%;height:6px;appearance:none;border-radius:8px;background:linear-gradient(to right,#05d8ff,#353f8f,#9334e8);outline:none;cursor:pointer}",
      ".ns-slider::-webkit-slider-thumb{appearance:none;width:18px;height:18px;border-radius:50%;background:#fff;border:2px solid #01e9ff;box-shadow:0 0 12px #00dfff}",
      ".ns-slider::-moz-range-thumb{width:18px;height:18px;border-radius:50%;background:#fff;border:2px solid #01e9ff;box-shadow:0 0 12px #00dfff}",
      ".ns-vol-value{font-size:13px;color:#d3eaff;text-align:right}",
      ".ns-vol-label{display:none}",
      ".ns-actions{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}",
      ".ns-btn{appearance:none;cursor:pointer;border:1px solid rgba(69,168,242,.72);border-radius:10px;padding:10px 6px;background:linear-gradient(#092245,#020b21);box-shadow:inset 0 1px rgba(255,255,255,.13),0 0 9px rgba(0,183,255,.11);color:#dfedff;text-transform:uppercase;font:800 12px/1.1 Inter,system-ui,sans-serif;letter-spacing:.08em;transition:filter .12s,transform .12s}",
      ".ns-btn:hover{filter:brightness(1.35)}",
      ".ns-btn:active{transform:scale(.98)}",
      ".ns-actions .ns-btn:nth-child(1){border-color:#00cafa;box-shadow:0 0 11px rgba(0,223,255,.28)}",
      ".ns-btn--primary,.ns-actions .ns-btn:nth-child(2){border-color:#ed22e6;background:linear-gradient(#43084f,#230a42);box-shadow:0 0 11px rgba(252,37,226,.25)}",
      ".ns-controls-card h2{margin-bottom:10px}",
      ".ns-controls-list{display:grid;grid-template-columns:1fr 1fr;gap:7px 8px}",
      ".ns-control-item{display:flex;align-items:center;gap:6px;color:#c6e5ff;font-size:11px;line-height:1.3}",
      ".ns-keyset{display:flex;gap:4px;flex:none}",
      ".ns-control-item kbd{min-width:26px;min-height:26px;padding:3px 5px;display:inline-flex;justify-content:center;align-items:center;border-radius:5px;border:1px solid #548bd6;background:#071529;color:#e8fbff;font-size:13px;font-family:inherit;font-weight:800}",
      ".ns-board-shell{position:relative;min-width:0;height:100%;background-color:#020411;background-position:center center;background-size:cover;background-repeat:no-repeat;display:flex;align-items:flex-start;justify-content:center;padding:24px 12px 0;overflow:hidden;isolation:isolate}",
      ".ns-board-shell:before{content:\"\";position:absolute;inset:0;background:linear-gradient(to right,rgba(0,0,0,.18),transparent 15%,transparent 85%,rgba(0,0,0,.1));z-index:0;pointer-events:none}",
      ".ns-reflection{position:absolute;inset:0;z-index:1;pointer-events:none;filter:blur(28px)}",
      ".ns-well{position:relative;z-index:2;flex:none;transform:translateX(clamp(-70px,-4vw,-20px));padding:9px;border-radius:23px;background:linear-gradient(120deg,rgba(6,200,255,.23),rgba(255,22,235,.22));border:2px solid #40dfff;box-shadow:0 0 0 2px rgba(23,28,132,.65),0 0 14px #00caff,0 0 33px rgba(0,200,255,.65),0 0 25px rgba(255,0,232,.28)}",
      ".ns-well:before{content:\"\";position:absolute;inset:-2px;border-radius:23px;border:2px solid transparent;border-right-color:#ff00e9;border-bottom-color:#ff00e9;pointer-events:none;box-shadow:3px 2px 15px rgba(255,30,240,.3)}",
      ".ns-well canvas{width:100%;height:100%;display:block;border-radius:12px;background:rgba(2,6,17,.9)}",
      ".ns-overlay{position:absolute;inset:9px;z-index:3;display:flex;align-items:center;justify-content:center;flex-direction:column;padding:20px;gap:8px;text-align:center;border-radius:12px;background:rgba(1,5,18,.82)}",
      ".ns-overlay[hidden]{display:none}",
      ".ns-overlay h2{font-size:28px;line-height:1.15;margin:0;color:#fff;text-shadow:0 0 12px #ef24e8}",
      ".ns-overlay p{color:#d4f5ff;font-size:13px;margin:0}",
      ".ns-floor-reflection{position:absolute;z-index:1;pointer-events:none;opacity:.80;filter:blur(2.4px);-webkit-mask-image:linear-gradient(to bottom,rgba(0,0,0,.7),transparent 90%);mask-image:linear-gradient(to bottom,rgba(0,0,0,.7),transparent 90%)}",
      ".ns-touch{display:none}",
      ".ns:focus-visible,.ns-btn:focus-visible,.ns-slider:focus-visible{outline:2px solid #fff;outline-offset:2px}",
      "@media(max-width:1220px){.ns-mid{grid-template-columns:360px minmax(0,1fr)}.ns-sidebar{padding:0 12px 12px;gap:7px}.ns-logo{max-width:340px}.ns-card{padding:10px}.ns-controls-list{gap:5px}.ns-top-row{grid-template-columns:98px 1fr}.ns-hold-card .ns-mini{width:63px;height:63px}}",
      "@media(max-width:860px){.ns{height:auto;min-height:100%;overflow:auto}.ns-mid{display:flex;flex-direction:column;min-height:100vh;height:auto}.ns-board-shell{order:1;min-height:100svh;height:100svh;padding:12px 4px 5px;overflow:hidden}.ns-sidebar{order:2;width:100%;max-width:100%;border-right:0;border-top:1px solid #0b8eb4;overflow:visible;padding:8px 12px 28px}.ns-logo{max-width:300px}.ns-brand-panel{display:block}.ns-logo{width:200px;margin:0 auto}.ns-well{transform:none}.ns-top-row{grid-template-columns:100px 1fr}.ns-touch{position:absolute;bottom:8px;left:50%;transform:translateX(-50%);z-index:4;display:grid;grid-template-columns:repeat(3,1fr);gap:7px;width:min(95vw,400px);touch-action:none}.ns-touch .ns-btn{padding:13px 6px;background:rgba(2,13,32,.86);font-size:12px;touch-action:none}.ns-floor-reflection{display:none}}",
      "@media(max-width:420px){.ns-top-row{grid-template-columns:88px minmax(0,1fr)}.ns-card{padding:8px}.ns-card h2{font-size:11px}.ns-controls-list{grid-template-columns:1fr 1fr}.ns-next-card .ns-next-row{gap:3px}}"
    ].join("\n");

    const root = document.createElement("div");
    root.className = "ns";
    root.setAttribute("role", "application");
    root.setAttribute("aria-label", "Neon Stack");
    root.style.background = "#000";

    const style = document.createElement("style");
    style.textContent = css;
    root.appendChild(style);

    const sky = document.createElement("canvas");
    sky.className = "ns-sky";
    sky.setAttribute("aria-hidden", "true");
    const blast = document.createElement("div");
    blast.className = "ns-blast";
    blast.setAttribute("aria-hidden", "true");

    const mid = document.createElement("div");
    mid.className = "ns-mid";

    const holdPanel = document.createElement("aside");
    holdPanel.className = "ns-sidebar";

    const head = document.createElement("div");
    head.className = "ns-brand-panel";
    const brand = document.createElement("div");
    brand.className = "ns-brand";
    const logo = document.createElement("img");
    logo.src = "data:image/webp;base64,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";
    logo.alt = "Neon Stack";
    logo.className = "ns-logo";
    brand.appendChild(logo);
    head.appendChild(brand);

    const topRow = document.createElement("div");
    topRow.className = "ns-top-row";
    const holdCard = document.createElement("section");
    holdCard.className = "ns-card ns-hold-card";
    const holdHeading = document.createElement("h2");
    holdHeading.textContent = "Hold";
    const holdCanvas = document.createElement("canvas");
    holdCanvas.className = "ns-mini";
    holdCanvas.width = 72;
    holdCanvas.height = 72;
    const holdEmpty = document.createElement("p");
    holdEmpty.className = "ns-empty";
    holdEmpty.textContent = "Empty";
    const holdHint = document.createElement("p");
    holdHint.className = "ns-empty";
    holdHint.textContent = "Press C to store or swap.";
    holdCard.append(holdHeading, holdCanvas, holdEmpty, holdHint);

    const nextPanel = document.createElement("section");
    nextPanel.className = "ns-card ns-next-card";
    const nextHeading = document.createElement("h2");
    nextHeading.textContent = "Next Pieces";
    const nextRow = document.createElement("div");
    nextRow.className = "ns-next-row";
    const nextCanvases = [];
    for (let n = 0; n < 3; n++) {
      const mini = document.createElement("canvas");
      mini.className = "ns-mini";
      mini.width = 72;
      mini.height = 72;
      nextRow.appendChild(mini);
      nextCanvases.push(mini);
    }
    nextPanel.append(nextHeading, nextRow);
    topRow.append(holdCard, nextPanel);

    const scorePanel = document.createElement("section");
    scorePanel.className = "ns-card ns-score-card";
    const statsHeading = document.createElement("h2");
    statsHeading.textContent = "Score";
    const scoreStat = statRow("Score");
    const levelStat = statRow("Level");
    const linesStat = statRow("Lines");
    scorePanel.append(statsHeading, scoreStat.row, levelStat.row, linesStat.row);
    const meter = document.createElement("div");
    meter.className = "ns-meter";
    const pips = [];
    for (let i = 0; i < 10; i++) { const pip = document.createElement("i"); meter.appendChild(pip); pips.push(pip); }
    const nextLevel = document.createElement("p");
    nextLevel.className = "ns-nextlevel";
    scorePanel.append(meter, nextLevel);

    const musicPanel = document.createElement("section");
    musicPanel.className = "ns-card ns-now-playing";
    const nowHead = document.createElement("div");
    nowHead.className = "ns-now-head";
    const nowTitle = document.createElement("strong");
    nowTitle.textContent = "♫  NOW PLAYING";
    const bars = document.createElement("div");
    bars.className = "ns-bars";
    bars.setAttribute("aria-hidden", "true");
    const barEls = [];
    for (let b = 0; b < 12; b++) { const bar = document.createElement("i"); bars.appendChild(bar); barEls.push(bar); }
    nowHead.append(nowTitle, bars);
    const songMeta = document.createElement("div");
    songMeta.className = "ns-songname";
    const songName = document.createElement("span");
    songName.textContent = music.songName();
    const soundLabel = document.createElement("span");
    soundLabel.textContent = "Sound on";
    soundLabel.style.fontSize = "12px";
    soundLabel.style.color = "#b9dcf4";
    songMeta.append(songName, soundLabel);
    const volumeRow = document.createElement("div");
    volumeRow.className = "ns-volume-row";
    const soundIcon = document.createElement("span");
    soundIcon.className = "ns-sound-icon";
    soundIcon.textContent = "🔊";
    const volume = document.createElement("input");
    volume.type = "range";
    volume.min = "0";
    volume.max = "100";
    volume.value = "30";
    volume.className = "ns-slider";
    volume.setAttribute("aria-label", "Music volume");
    const volumeValue = document.createElement("span");
    volumeValue.className = "ns-vol-value";
    volumeValue.textContent = "30%";
    volumeRow.append(soundIcon, volume, volumeValue);
    const volumeLabel = document.createElement("label");
    volumeLabel.className = "ns-vol-label";
    volumeLabel.textContent = "Music volume 30%";
    const actions = document.createElement("div");
    actions.className = "ns-actions";
    const pauseBtn = document.createElement("button");
    pauseBtn.type = "button";
    pauseBtn.className = "ns-btn";
    pauseBtn.textContent = "Pause";
    const restartBtn = document.createElement("button");
    restartBtn.type = "button";
    restartBtn.className = "ns-btn ns-btn--primary";
    restartBtn.textContent = "Restart";
    const randomSong = document.createElement("button");
    randomSong.type = "button";
    randomSong.className = "ns-btn";
    randomSong.textContent = "Random Song";
    const muteBtn = document.createElement("button");
    muteBtn.type = "button";
    muteBtn.className = "ns-btn";
    muteBtn.textContent = "Mute";
    actions.append(pauseBtn, restartBtn, randomSong, muteBtn);
    musicPanel.append(nowHead, songMeta, volumeRow, volumeLabel, actions);

    const controlsPanel = document.createElement("section");
    controlsPanel.className = "ns-card ns-controls-card";
    const controlsHeading = document.createElement("h2");
    controlsHeading.textContent = "Controls";
    const controlsList = document.createElement("div");
    controlsList.className = "ns-controls-list";
    function controlItem(keys, label) {
      const row = document.createElement("div");
      row.className = "ns-control-item";
      const keyset = document.createElement("div");
      keyset.className = "ns-keyset";
      keys.forEach(function (key) {
        const k = document.createElement("kbd");
        k.textContent = key;
        keyset.appendChild(k);
      });
      const text = document.createElement("span");
      text.textContent = label;
      row.append(keyset, text);
      return row;
    }
    controlsList.append(
      controlItem(["←","→"], "Move left / right"),
      controlItem(["Space"], "Hard drop"),
      controlItem(["Z","X"], "Rotate (CCW / CW)"),
      controlItem(["C"], "Hold piece")
    );
    controlsPanel.append(controlsHeading, controlsList);

    holdPanel.append(head, topRow, scorePanel, musicPanel, controlsPanel);

    const boardShell = document.createElement("section");
    boardShell.className = "ns-board-shell";
    boardShell.style.backgroundImage = "url(" + EMBEDDED_BACKGROUND + ")";
    const boardTop = document.createElement("div"); boardTop.className = "ns-board-top";
    const reflection = document.createElement("canvas");
    reflection.className = "ns-reflection";
    reflection.setAttribute("aria-hidden", "true");
    const floorReflection = document.createElement("canvas");
    floorReflection.className = "ns-floor-reflection";
    floorReflection.setAttribute("aria-hidden", "true");
    const well = document.createElement("div");
    well.className = "ns-well";
    const canvas = document.createElement("canvas");
    canvas.setAttribute("aria-hidden", "true");
    const overlay = document.createElement("div");
    overlay.className = "ns-overlay";
    overlay.setAttribute("role", "status");
    overlay.setAttribute("aria-live", "polite");
    const overlayTitle = document.createElement("h2");
    const overlayBody = document.createElement("p");
    overlay.append(overlayTitle, overlayBody);
    well.append(canvas, overlay);
    const mobileStats = document.createElement("div");
    mobileStats.className = "ns-mobile-stats";
    const mobileScore = document.createElement("span");
    const mobileLevel = document.createElement("span");
    const mobileLines = document.createElement("span");
    mobileStats.append(mobileScore, mobileLevel, mobileLines);
    const touch = document.createElement("div");
    touch.className = "ns-touch";
    [["left","◀"],["soft","▼"],["right","▶"],["ccw","↺ Rotate"],["hard","⬇ Drop"],["hold","Hold"]].forEach(function(a){
      const b=document.createElement("button");b.type="button";b.className="ns-btn";b.textContent=a[1];b.dataset.action=a[0];
      b.addEventListener("pointerdown",function(e){e.preventDefault();music.unlock();session.press(a[0]);try{b.setPointerCapture(e.pointerId);}catch(_){} });
      function release(e){e.preventDefault();session.release(a[0]);}
      b.addEventListener("pointerup",release);b.addEventListener("pointercancel",release);b.addEventListener("lostpointercapture",function(){session.release(a[0]);});
      touch.appendChild(b);
    });
    const boardFoot = document.createElement("p"); boardFoot.className = "ns-board-foot";
    boardShell.append(mobileStats, boardTop, reflection, floorReflection, well, touch, boardFoot);

    const bannerEl = document.createElement("div");
    bannerEl.className = "ns-banner";
    const bannerTitle = document.createElement("strong");
    const bannerDetail = document.createElement("span");
    bannerEl.append(bannerTitle, bannerDetail);
    holdPanel.append(bannerEl);

    const glowSelect = document.createElement("select");
    glowSelect.className = "ns-glow-select";
    [["0","Off"],["0.3","Subtle"],["0.65","Normal"],["1","High"]].forEach(function(a){const op=document.createElement("option");op.value=a[0];op.textContent=a[1];glowSelect.appendChild(op);});
    glowSelect.value = "0.65";
    glowSelect.style.display = "none";
    musicPanel.appendChild(glowSelect);

    const pauseBtnPanel = pauseBtn;
    const restartBtnPanel = restartBtn;
    const muteBtnPanel = muteBtn;
    const keys = document.createElement("p");
    keys.className = "ns-keys";

    mid.append(holdPanel, boardShell);
    root.append(sky, blast, mid, keys);
    el.replaceChildren(root);
    // Bind the one actual set of controls. The previous layout lost these listeners.
    pauseBtn.addEventListener("click", function () {
      session.press("pause");
      sync(session.snapshot());
    });
    restartBtn.addEventListener("click", function () {
      session.press("restart");
      sync(session.snapshot());
    });
    muteBtn.addEventListener("click", function () {
      music.unlock();
      music.toggle();
      sync(session.snapshot());
    });
    randomSong.addEventListener("click", function () {
      music.unlock();
      songName.textContent = music.random();
      sync(session.snapshot());
    });
    volume.addEventListener("input", function () {
      music.unlock();
      music.setVolume(Number(volume.value) / 100);
      volumeValue.textContent = volume.value + "%";
      volumeLabel.textContent = "Music volume " + volume.value + "%";
    });
    function statRow(label) {
      const row = document.createElement("div");
      row.className = "ns-stat";
      const span = document.createElement("span");
      span.textContent = label;
      const strong = document.createElement("b");
      strong.textContent = "0";
      row.append(span, strong);
      return { row: row, value: strong };
    }

    function addKeys(parent, items) {
      items.forEach(function (item, index) {
        if (index) parent.appendChild(document.createTextNode("  "));
        item.keys.forEach(function (key, keyIndex) {
          if (keyIndex) parent.appendChild(document.createTextNode("/"));
          const kbd = document.createElement("kbd");
          kbd.textContent = key;
          parent.appendChild(kbd);
        });
        parent.appendChild(document.createTextNode(" " + item.label));
      });
    }

    function isOpen() {
      if (!root.isConnected) return false;
      const rect = root.getBoundingClientRect();
      return rect.width > 0 && rect.height > 0;
    }

    function actionOf(event) {
      const code = event.code;
      const modified = event.ctrlKey || event.metaKey || event.altKey;
      if (code === "ArrowLeft") return "left";
      if (code === "ArrowRight") return "right";
      if (code === "ArrowDown") return "soft";
      if (code === "Space") return "hard";
      if (code === "ArrowUp") return "cw";
      if (code === "KeyX" && !modified) return "cw";
      if (code === "KeyZ" && !modified) return "ccw";
      if (code === "ControlLeft" || code === "ControlRight") return "ccw";
      if (code === "KeyC" && !modified) return "hold";
      if (code === "KeyP" && !modified) return "pause";
      if (code === "KeyM" && !modified) return "mute";
      if (code === "KeyR" && !modified) return "restart";
      if (code === "Escape") return "quit";
      return null;
    }

    function onKeyDown(event) {
      if (dead) return;
      if (event.target && /^(INPUT|SELECT|TEXTAREA)$/.test(event.target.tagName)) return;
      const action = actionOf(event);
      if (!action || !isOpen()) return;
      event.preventDefault();
      music.unlock();
      if (event.repeat) return;
      if (action === "mute") {
        music.toggle();
        sync(session.snapshot());
        return;
      }
      session.press(action);
      sync(session.snapshot());
    }

    function onKeyUp(event) {
      if (dead) return;
      const action = actionOf(event);
      if (!action || !isOpen()) return;
      if (action === "left" || action === "right" || action === "soft") {
        event.preventDefault();
        session.release(action);
      }
    }

    function onPointer() {
      if (!dead) music.unlock();
    }

    globalThis.addEventListener("keydown", onKeyDown, { capture: true, signal: ac.signal });
    globalThis.addEventListener("keyup", onKeyUp, { capture: true, signal: ac.signal });
    root.addEventListener("pointerdown", onPointer);

    function measure() {
      const narrow = root.clientWidth <= 860;
      const frame = 22; // 9px padding + 2px border on each side
      const usableWidth = Math.max(120, boardShell.clientWidth - (narrow ? 12 : 36));
      const shellHeight = boardShell.clientHeight || root.clientHeight;
      const reserve = narrow ? 160 : 95; // floor reflection desktop; touch controls mobile
      const usableHeight = Math.max(200, shellHeight - reserve);
      const cell = Math.max(7, Math.floor(Math.min((usableWidth-frame)/COLS, (usableHeight-frame)/ROWS)));
      const w = (cell * COLS + frame) + "px";
      const h = (cell * ROWS + frame) + "px";
      if (well.style.width !== w) well.style.width = w;
      if (well.style.height !== h) well.style.height = h;
    }

    function traceRound(ctx, x, y, w, h, r) {
      const rr = Math.max(0, Math.min(r, w / 2, h / 2));
      ctx.beginPath();
      ctx.moveTo(x + rr, y);
      ctx.arcTo(x + w, y, x + w, y + h, rr);
      ctx.arcTo(x + w, y + h, x, y + h, rr);
      ctx.arcTo(x, y + h, x, y, rr);
      ctx.arcTo(x, y, x + w, y, rr);
      ctx.closePath();
    }

    function drawNeon(ctx,x,y,size,id,alpha){
      const color=COLORS[id]||'#00f0ff', pad=Math.max(1,size*.075),rx=x+pad,ry=y+pad,s=size-pad*2;
      if(s<=1)return;
      ctx.save();ctx.globalAlpha=alpha;
      ctx.shadowColor=color;ctx.shadowBlur=size*.58;
      ctx.fillStyle=color;traceRound(ctx,rx,ry,s,s,s*.15);ctx.fill();ctx.shadowBlur=0;
      const glass=ctx.createLinearGradient(rx,ry,rx+s,ry+s);
      glass.addColorStop(0,'rgba(255,255,255,.54)');glass.addColorStop(.31,'rgba(13,31,61,.48)');glass.addColorStop(.55,'rgba(255,255,255,.07)');glass.addColorStop(1,'rgba(4,9,31,.52)');
      ctx.fillStyle=glass;traceRound(ctx,rx+1,ry+1,s-2,s-2,s*.12);ctx.fill();
      ctx.strokeStyle='rgba(255,255,255,.78)';ctx.lineWidth=Math.max(.7,size*.034);
      traceRound(ctx,rx+2,ry+2,s-4,s-4,s*.1);ctx.stroke();
      ctx.globalAlpha=alpha*(.2+.14*Math.sin(clock*.003+x*.09+y*.1));
      ctx.strokeStyle='#fff';ctx.lineWidth=1;
      for(let a=0;a<3;a++){const ly=ry+s*(.28+a*.19);ctx.beginPath();ctx.moveTo(rx+4,ly);ctx.lineTo(rx+s-4,ly);ctx.stroke();}
      ctx.restore();
    }

    function drawGhost(ctx, x, y, size, color) {
      const pad = Math.max(1, size * 0.1);
      ctx.save();
      ctx.globalAlpha = 0.8;
      ctx.strokeStyle = color;
      ctx.shadowColor = color;
      ctx.shadowBlur = 12;
      ctx.lineWidth = Math.max(1.5, size * 0.07);
      traceRound(ctx, x + pad, y + pad, size - pad * 2, size - pad * 2, Math.max(2, size * 0.14));
      ctx.stroke();
      ctx.restore();
    }

    function spawnBlast(snap) {
      const rows = snap.clearingRows;
      let ySum = 0;
      for (let i = 0; i < rows.length; i++) {
        const y = rows[i];
        ySum += y;
        for (let x = 0; x < COLS; x++) {
          const id = snap.board[y][x] || "T";
          const color = COLORS[id];
          for (let p = 0; p < 6; p++) {
            const angle = fxRand() * Math.PI * 2;
            const speed = 0.012 + fxRand() * 0.028;
            shards.push({
              x: x + 0.35 + fxRand() * 0.3,
              y: y + 0.35 + fxRand() * 0.3,
              vx: Math.cos(angle) * speed,
              vy: Math.sin(angle) * speed - 0.008,
              rot: fxRand() * Math.PI,
              vr: (fxRand() - 0.5) * 0.4,
              w: 0.08 + fxRand() * 0.14,
              h: 0.08 + fxRand() * 0.16,
              color: color,
              life: 1,
            });
          }
        }
      }
      flash = 1;
      shock = { y: ySum / rows.length + 0.5, life: 1, power: rows.length };
    }

    function stepEffects(dt, snap) {
      const mark = snap.clearingRows.join(",");
      if (mark && mark !== sparkMark) {
        sparkMark = mark;
        spawnBlast(snap);
      } else if (!mark) {
        sparkMark = "";
      }
      flash = Math.max(0, flash - dt / 260);
      if (shock) {
        shock.life -= dt / 620;
        if (shock.life <= 0) shock = null;
      }
      for (let i = shards.length - 1; i >= 0; i--) {
        const shard = shards[i];
        shard.x += shard.vx * dt;
        shard.y += shard.vy * dt;
        shard.vy += 0.00002 * dt;
        shard.rot += shard.vr * dt * 0.05;
        shard.life -= dt / 760;
        if (shard.life <= 0) shards.splice(i, 1);
      }
    }

    function paintSky() {
      const cssW = root.clientWidth;
      const cssH = root.clientHeight;
      if (cssW < 2 || cssH < 2) return;
      const dpr = Math.min(2, globalThis.devicePixelRatio || 1);
      const bw = Math.round(cssW * dpr);
      const bh = Math.round(cssH * dpr);
      if (sky.width !== bw || sky.height !== bh) {
        sky.width = bw;
        sky.height = bh;
      }
      const ctx = sky.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      const bg=ctx.createLinearGradient(0,0,0,cssH);
      bg.addColorStop(0,'#030b25');bg.addColorStop(.48,'#080c2d');bg.addColorStop(1,'#061322');
      ctx.fillStyle=bg;ctx.fillRect(0,0,cssW,cssH);
      const t=clock*.00017;
      for(let band=0;band<7;band++){
        const cx=cssW*(.05+band*.155)+Math.sin(t*2+band)*cssW*.06;
        const gradient=ctx.createLinearGradient(cx-170,0,cx+170,cssH*.82);
        const colors=['30,247,201','77,151,255','199,71,255','64,250,225'];
        gradient.addColorStop(0,'rgba('+colors[band%4]+',0)');
        gradient.addColorStop(.32,'rgba('+colors[band%4]+',.13)');
        gradient.addColorStop(.63,'rgba('+colors[band%4]+',.03)');
        gradient.addColorStop(1,'rgba('+colors[band%4]+',0)');
        ctx.save();ctx.translate(Math.sin(t+band)*55,0);ctx.transform(1,0,Math.sin(t*.8+band)*.3,1,0,0);
        ctx.fillStyle=gradient;ctx.beginPath();ctx.moveTo(cx-95,-20);
        ctx.bezierCurveTo(cx+140,cssH*.17,cx-110,cssH*.55,cx+90,cssH*.83);
        ctx.lineTo(cx+210,cssH*.83);ctx.bezierCurveTo(cx-20,cssH*.51,cx+280,cssH*.14,cx+45,-20);ctx.fill();ctx.restore();
      }
      for(let i=0;i<110;i++){
        const x=((i*131.71)%997)/997*cssW,y=((i*73.19)%601)/601*cssH;
        ctx.globalAlpha=.18+.42*(.5+.5*Math.sin(clock*.001+i));
        ctx.fillStyle='#e5faff';ctx.fillRect(x,y,i%11===0?2:1,i%11===0?2:1);
      }ctx.globalAlpha=1;
      ctx.strokeStyle='rgba(41,204,235,.14)';ctx.lineWidth=1;ctx.beginPath();
      const horizon=cssH*.79;
      for(let x=-cssW;x<cssW*2;x+=65){ctx.moveTo(cssW/2,horizon);ctx.lineTo(x,cssH);}
      for(let k=1;k<10;k++){const yy=horizon+(cssH-horizon)*Math.pow(k/10,1.6);ctx.moveTo(0,yy);ctx.lineTo(cssW,yy);}
      ctx.stroke();
      if (shock && well.getBoundingClientRect) {
        const wr = well.getBoundingClientRect();
        const rr = root.getBoundingClientRect();
        const cx = wr.left - rr.left + wr.width / 2;
        const cy = wr.top - rr.top + (shock.y / ROWS) * wr.height;
        const radius = (1 - shock.life) * Math.max(wr.width, wr.height) * 1.35;
        ctx.save();
        ctx.strokeStyle = "rgba(255,255,255," + shock.life + ")";
        ctx.shadowColor = "#ff2bd6";
        ctx.shadowBlur = 28;
        ctx.lineWidth = 6 + shock.life * 14;
        ctx.beginPath();
        ctx.arc(cx, cy, Math.max(4, radius), 0, Math.PI * 2);
        ctx.stroke();
        ctx.strokeStyle = "rgba(0,240,255," + (shock.life * 0.9) + ")";
        ctx.lineWidth = 3;
        ctx.beginPath();
        ctx.arc(cx, cy, Math.max(4, radius * 0.72), 0, Math.PI * 2);
        ctx.stroke();
        ctx.restore();
      }
    }

    function paintMini(mini, id) {
      const cssSize = Math.max(48, Math.round(mini.clientWidth || 68));
      const dpr = Math.min(2, globalThis.devicePixelRatio || 1);
      const px = Math.round(cssSize * dpr);
      if (mini.width !== px || mini.height !== px) {
        mini.width = px;
        mini.height = px;
      }
      const ctx = mini.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.fillStyle = "#07060f";
      ctx.fillRect(0, 0, cssSize, cssSize);
      if (!id) {
        ctx.strokeStyle = "#00f0ff";
        ctx.globalAlpha = 0.45;
        ctx.lineWidth = 2;
        ctx.strokeRect(16, 16, 24, 24);
        ctx.globalAlpha = 1;
        return;
      }
      const matrix = ROTATIONS[id][0];
      let minC = 4;
      let minR = 4;
      let maxC = -1;
      let maxR = -1;
      const blocks = [];
      for (let r = 0; r < 4; r++) {
        for (let c = 0; c < 4; c++) {
          if (!matrix[r][c]) continue;
          blocks.push([c, r]);
          if (c < minC) minC = c;
          if (r < minR) minR = r;
          if (c > maxC) maxC = c;
          if (r > maxR) maxR = r;
        }
      }
      const bw = maxC - minC + 1;
      const bh = maxR - minR + 1;
      const size = Math.floor(Math.min((cssSize - 12) / bw, (cssSize - 12) / bh));
      const ox = Math.floor((cssSize - bw * size) / 2);
      const oy = Math.floor((cssSize - bh * size) / 2);
      for (let i = 0; i < blocks.length; i++) {
        drawNeon(ctx, ox + (blocks[i][0] - minC) * size, oy + (blocks[i][1] - minR) * size, size, id, 1);
      }
    }

    function paintMinis(snap) {
      const sig = (snap.holdId || "-") + "|" + snap.queue.join(",");
      if (sig === miniSig) return;
      miniSig = sig;
      paintMini(holdCanvas, snap.holdId);
      for (let i = 0; i < nextCanvases.length; i++) paintMini(nextCanvases[i], snap.queue[i] || null);
    }

    function drawWell(snap) {
      const cssW = canvas.clientWidth;
      const cssH = canvas.clientHeight;
      if (cssW < 2 || cssH < 2) return;
      const dpr = Math.min(2, globalThis.devicePixelRatio || 1);
      const bw = Math.round(cssW * dpr);
      const bh = Math.round(cssH * dpr);
      if (canvas.width !== bw || canvas.height !== bh) {
        canvas.width = bw;
        canvas.height = bh;
      }
      const ctx = canvas.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      if (flash > 0) {
        ctx.translate(Math.sin(clock * 0.09) * flash * 8, Math.cos(clock * 0.13) * flash * 6);
      }
      const cell = cssW / COLS;
      ctx.fillStyle = "#07060f";
      ctx.fillRect(-20, -20, cssW + 40, cssH + 40);
      ctx.strokeStyle = "rgba(0,240,255,0.12)";
      ctx.lineWidth = 1;
      ctx.beginPath();
      for (let x = 0; x <= COLS; x++) {
        ctx.moveTo(Math.round(x * cell) + 0.5, 0);
        ctx.lineTo(Math.round(x * cell) + 0.5, cssH);
      }
      for (let y = 0; y <= ROWS; y++) {
        ctx.moveTo(0, Math.round(y * cell) + 0.5);
        ctx.lineTo(cssW, Math.round(y * cell) + 0.5);
      }
      ctx.stroke();

      const clearing = {};
      for (let i = 0; i < snap.clearingRows.length; i++) clearing[snap.clearingRows[i]] = true;
      for (let y = 0; y < ROWS; y++) {
        if (clearing[y]) {
          ctx.save();
          ctx.globalAlpha = 0.85;
          ctx.fillStyle = "#fff";
          ctx.shadowColor = "#ff2bd6";
          ctx.shadowBlur = 24;
          ctx.fillRect(0, y * cell, cssW, cell);
          ctx.restore();
          continue;
        }
        for (let x = 0; x < COLS; x++) {
          const id = snap.board[y][x];
          if (id) drawNeon(ctx, x * cell, y * cell, cell, id, 1);
        }
      }
      if (snap.current && snap.ghostY != null) {
        const ghost = { id: snap.current.id, rot: snap.current.rot, x: snap.current.x, y: snap.ghostY };
        const ghosts = cellsOf(ghost);
        for (let i = 0; i < ghosts.length; i++) {
          drawGhost(ctx, ghosts[i][0] * cell, ghosts[i][1] * cell, cell, COLORS[ghost.id]);
        }
      }
      if (snap.current) {
        const blocks = cellsOf(snap.current);
        for (let i = 0; i < blocks.length; i++) {
          drawNeon(ctx, blocks[i][0] * cell, blocks[i][1] * cell, cell, snap.current.id, 1);
        }
      }
      for (let i = 0; i < shards.length; i++) {
        const shard = shards[i];
        ctx.save();
        ctx.translate(shard.x * cell, shard.y * cell);
        ctx.rotate(shard.rot);
        ctx.globalAlpha = Math.max(0, shard.life);
        ctx.fillStyle = shard.color;
        ctx.shadowColor = shard.color;
        ctx.shadowBlur = 18;
        ctx.beginPath();
        ctx.moveTo(-shard.w * cell, shard.h * cell * 0.4);
        ctx.lineTo(shard.w * cell, shard.h * cell * 0.2);
        ctx.lineTo(0, -shard.h * cell);
        ctx.closePath();
        ctx.fill();
        ctx.restore();
      }
      if (shock) {
        const radius = (1 - shock.life) * cell * (6 + shock.power * 3.2);
        ctx.save();
        ctx.strokeStyle = "rgba(255,255,255," + shock.life + ")";
        ctx.shadowColor = "#00f0ff";
        ctx.shadowBlur = 22;
        ctx.lineWidth = 3 + shock.life * 8;
        ctx.beginPath();
        ctx.arc(cssW / 2, shock.y * cell, Math.max(2, radius), 0, Math.PI * 2);
        ctx.stroke();
        ctx.restore();
      }
      if (flash > 0.02) {
        ctx.fillStyle = "rgba(255,255,255," + (flash * 0.72) + ")";
        ctx.fillRect(-20, -20, cssW + 40, cssH + 40);
      }
    }

    function paintReflection(snap) {
      const strength = Number(glowSelect.value);
      if (!strength) {reflection.style.opacity="0";return;}
      reflection.style.opacity=String(strength);
      const w=reflection.clientWidth,h=reflection.clientHeight;
      if (w<5||h<5)return;
      const scale=.36;
      const pw=Math.ceil(w*scale),ph=Math.ceil(h*scale);
      if(reflection.width!==pw||reflection.height!==ph){reflection.width=pw;reflection.height=ph;}
      const ctx=reflection.getContext("2d");ctx.clearRect(0,0,pw,ph);
      const rect=well.getBoundingClientRect(), rr=reflection.getBoundingClientRect();
      const x0=(rect.left-rr.left+10)*scale,y0=(rect.top-rr.top+10)*scale;
      const cell=(rect.width-20)/COLS*scale;
      ctx.globalCompositeOperation="lighter";
      for(let y=0;y<ROWS;y++)for(let x=0;x<COLS;x++){
        const id=snap.board[y][x];if(!id)continue;
        ctx.fillStyle=COLORS[id];ctx.globalAlpha=.38;
        ctx.fillRect(x0+x*cell-4,y0+y*cell-4,cell+8,cell+8);
      }
      if(snap.current){ctx.fillStyle=COLORS[snap.current.id];ctx.globalAlpha=.55;
        cellsOf(snap.current).forEach(function(a){ctx.fillRect(x0+a[0]*cell-7,y0+a[1]*cell-7,cell+14,cell+14);});}
      ctx.globalCompositeOperation="source-over";ctx.globalAlpha=1;
    }

    function paintFloorReflection() {
      const wr = well.getBoundingClientRect();
      const br = boardShell.getBoundingClientRect();
      const available = Math.max(0, br.bottom - wr.bottom);
      const h = Math.min(90, available - 4);
      if (root.clientWidth <= 860 || h <= 10) {
        floorReflection.style.display = "none";
        return;
      }
      floorReflection.style.display = "block";
      const w = Math.round(wr.width);
      floorReflection.style.left = Math.round(wr.left - br.left) + "px";
      floorReflection.style.top = Math.round(wr.bottom - br.top + 2) + "px";
      floorReflection.style.width = w + "px";
      floorReflection.style.height = Math.floor(h) + "px";
      // Draw only the bottom of the playfield, vertically mirrored onto the neon floor.
      const fw = Math.max(1, w), fh = Math.max(1, Math.floor(h));
      if (floorReflection.width !== fw || floorReflection.height !== fh) {
        floorReflection.width = fw;
        floorReflection.height = fh;
      }
      const c = floorReflection.getContext("2d");
      c.clearRect(0, 0, fw, fh);
      c.save();
      c.translate(0, fh); c.scale(1, -1);
      c.globalAlpha = 0.88;
      c.drawImage(canvas, 0, Math.round(canvas.height * .83), canvas.width, Math.max(1, Math.round(canvas.height * .17)),
                       11, 0, fw-22, fh);
      c.restore();
      const frameGlow = c.createLinearGradient(0,0,fw,0);
      frameGlow.addColorStop(0,"rgba(0,235,255,.5)");
      frameGlow.addColorStop(0.55,"rgba(40,140,255,.35)");
      frameGlow.addColorStop(1,"rgba(255,34,229,.5)");
      c.fillStyle = frameGlow;
      c.fillRect(0,0,fw,2);
    }

    function sync(snap) {
      root.dataset.state = snap.status;
      root.dataset.score = String(snap.score);
      root.dataset.lines = String(snap.lines);
      root.dataset.level = String(snap.level);
      root.dataset.audio = music.label();
      root.dataset.levelRms = music.level().toFixed(4);
      root.dataset.effect = (flash > 0.05 || shock || shards.length) ? "shockwave" : "";
      root.dataset.shards = String(shards.length);
      blast.style.opacity = String(Math.min(0.92, flash));
      mobileScore.textContent = "SCORE " + snap.score.toLocaleString("en-US");
      mobileLevel.textContent = "LEVEL " + snap.level;
      mobileLines.textContent = "LINES " + snap.lines;
      scoreStat.value.textContent = snap.score.toLocaleString("en-US");
      levelStat.value.textContent = String(snap.level);
      linesStat.value.textContent = String(snap.lines);
      if (snap.score !== seenScore) {
        seenScore = snap.score;
        scorePop = 180;
      }
      scoreStat.value.classList.toggle("pop", scorePop > 0);
      for (let i = 0; i < pips.length; i++) pips[i].classList.toggle("on", i < snap.linesInto);
      nextLevel.textContent = snap.linesToNext + " to next level";
      holdEmpty.hidden = !!snap.holdId;
      holdPanel.classList.toggle("is-locked", !!snap.holdLocked);
      const audioLabel = music.label();
      soundLabel.textContent = audioLabel === "muted" ? "Muted" : (audioLabel === "off" ? "Tap to enable audio" : "Sound on");
      const paused = snap.status === "paused";
      pauseBtn.textContent = paused ? "Resume" : "Pause";
      pauseBtnPanel.textContent = paused ? "Resume" : "Pause";
      const muted = audioLabel === "muted";
      muteBtn.textContent = muted ? "Unmute" : "Mute";
      muteBtnPanel.textContent = muted ? "Unmute" : "Mute";
      const rms = music.level();
      for (let i = 0; i < barEls.length; i++) {
        const h = audioLabel === "playing" ? 4 + Math.min(14, rms * 80 + ((i * 3 + clock / 80) % 5)) : 4;
        barEls[i].style.height = h + "px";
      }
      if (snap.banner) {
        bannerTitle.textContent = snap.banner.title;
        bannerDetail.textContent = snap.banner.detail || "";
      } else {
        bannerTitle.textContent = "";
        bannerDetail.textContent = "Hard drops score more than soft drops.";
      }
      const showOverlay = snap.status === "paused" || snap.status === "gameover" || snap.status === "stopped";
      overlay.hidden = !showOverlay;
      if (snap.status === "paused") {
        overlayTitle.textContent = "Paused";
        overlayBody.textContent = "Press P to resume. R restarts. Esc quits.";
      } else if (snap.status === "gameover") {
        overlayTitle.textContent = "The stack reached the top";
        overlayBody.textContent = "Score " + snap.score.toLocaleString("en-US") + ". Press R to restart.";
      } else if (snap.status === "stopped") {
        overlayTitle.textContent = "Stopped";
        overlayBody.textContent = "Press R to play again.";
      } else {
        overlayTitle.textContent = "";
        overlayBody.textContent = "";
      }
      paintMinis(snap);
      paintReflection(snap);
      drawWell(snap);
      paintFloorReflection();
    }

    function frame(now) {
      if (dead) return;
      const dt = Math.min(48, Math.max(0, now - lastNow));
      lastNow = now;
      clock = now;
      if (scorePop > 0) scorePop -= dt;
      session.tick(dt);
      const snap = session.snapshot();
      stepEffects(dt, snap);
      measure();
      sync(snap);
      raf = globalThis.requestAnimationFrame(frame);
    }

    measure();
    sync(session.snapshot());
    raf = globalThis.requestAnimationFrame(frame);
    music.unlock();

    if (document.body && document.body.hasAttribute("data-game-player")) {
      root.tabIndex = 0;
      try { root.focus({ preventScroll: true }); } catch (err) { root.focus(); }
    }

    function destroy() {
      if (dead) return;
      dead = true;
      ac.abort();
      root.removeEventListener("pointerdown", onPointer);
      if (raf) globalThis.cancelAnimationFrame(raf);
      music.stop();
      mounts.delete(el);
      if (el.contains(root)) el.replaceChildren();
    }

    const api = { destroy: destroy };
    mounts.set(el, api);
    return api;
  }

  globalThis.DESKTOP_GAMES = globalThis.DESKTOP_GAMES || {};
  globalThis.DESKTOP_GAMES["neon-stack"] = {
    id: "neon-stack",
    title: "Neon Stack",
    mount: mount,
  };

  const testing = typeof process !== "undefined" && process.env && process.env.NEON_TEST === "1";
  if (testing) globalThis.__NEON_CREATE__ = createSession;

  function bootPlayer() {
    const body = document.body;
    if (!body || !body.hasAttribute("data-game-player")) return;
    const host = document.createElement("div");
    host.style.position = "fixed";
    host.style.inset = "0";
    host.style.width = "100%";
    host.style.height = "100%";
    host.style.margin = "0";
    document.documentElement.style.height = "100%";
    document.documentElement.style.background = "#05040c";
    body.style.margin = "0";
    body.style.height = "100%";
    body.style.overflow = "auto";
    body.style.background = "#05040c";
    body.appendChild(host);
    globalThis.DESKTOP_GAMES["neon-stack"].mount(host);
  }

  if (typeof document !== "undefined") {
    if (document.body) bootPlayer();
    else document.addEventListener("DOMContentLoaded", bootPlayer);
  }
})();
