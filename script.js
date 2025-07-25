// 16x9 blocks of 43x43
// 33ms/frame

//for (let i = 0; i < packetDmgs.length; i++) packetDmgs[i] = 80;

let FRAME_TIME = 33;  // ms

const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
const loading = document.getElementById('loading');
const startButton = document.getElementById('startButton');

const MAX_LEVELS = 14;
let startTime = null;
let frameTimer = null;
let currentLevel = 0;
let nextLevel = (currentLevel + 1) % MAX_LEVELS;
let frameCount = 0;

let mouseX = 0;
let mouseY = 0;
let mouseDown = false;
let keys = {
  A: false,
  D: false,
  Tab: false,
  Space: false,
};

let borderImage;
let levelData = [];
const lvlImages = [];
const lvlBgImages = [];
const packetsImages = [];
const firewallsImages = [];
const beamImages = [];
const beamTipImages = [];
const mirrorImages = [];
const proxyImages = [];
const cursorImage = new Image();
cursorImage.src = "sprites/cursor_0.png";
const bgTextureMap = [0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14];

let gameWidth;
let gameHeight;

const packetsN = [24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 61, 62, 63, 65, 67, 69, 71, 73, 75];
const firewallsN = [58, 59, 60, 61, 62, 63, 65, 67, 68, 69, 70, 71, 72, 74, 76];

let beams = [];
let packetDmgs = [];
let firewallDmgs = [];
let rotatingMirrors = [];
let fixedMirrors = [];

let proxyAngle = 0;
let beamColor = "cyan";
let selectedMirror = null;
let lastSelectedMirror = null;
let remainingAngle = 0;
let cursorSize = 1.0;
const CURSOR_FACTOR = 1.18;
const CURSOR_MAX_DIST2 = 0.005;


function formatTimeInterval(date1, date2) {
  let diffMs = Math.abs(date2 - date1);

  let totalSeconds = Math.floor(diffMs / 1000);
  let hours = Math.floor(totalSeconds / 3600);
  let minutes = Math.floor((totalSeconds % 3600) / 60);
  let seconds = totalSeconds % 60;
  let deciseconds = Math.floor((diffMs % 1000) / 100);

  const pad = (num) => String(num).padStart(2, '0');

  if (hours > 0) {
    return `${hours}:${pad(minutes)}:${pad(seconds)}`;
    //return `${hours}:${pad(minutes)}:${pad(seconds)}.${deciseconds}`;
  } else {
    return `${pad(minutes)}:${pad(seconds)}`;
    //return `${pad(minutes)}:${pad(seconds)}.${deciseconds}`;
  }
}

function findClosestRayIntersection(v0, v1, quads) {
  const EPSILON = 1e-5;
  let closestQuad = null;
  let closestPoint = null;
  let closestSide = null;
  let minDistSq = Infinity;

  // Direction of the ray
  const dx = v1[0] - v0[0];
  const dy = v1[1] - v0[1];

  function rayIntersectsSegment(p, q) {
    const rx = dx;
    const ry = dy;
    const sx = q[0] - p[0];
    const sy = q[1] - p[1];

    const rxs = rx * sy - ry * sx;
    if (Math.abs(rxs) < EPSILON) return null; // Parallel or collinear

    const t = ((p[0] - v0[0]) * sy - (p[1] - v0[1]) * sx) / rxs;
    const u = ((p[0] - v0[0]) * ry - (p[1] - v0[1]) * rx) / rxs;

    if (t > EPSILON && u >= 0 && u <= 1) {
      return [v0[0] + t * rx, v0[1] + t * ry];
    }
    return null;
  }

  for (let n = 0; n < quads.length; n++) {
    for (let i = 0; i < 4; i++) {
      const p1 = quads[n][i];
      const p2 = quads[n][(i + 1) % 4]; // Wrap around

      const intersection = rayIntersectsSegment(p1, p2);
      if (intersection) {
        const dx = intersection[0] - v0[0];
        const dy = intersection[1] - v0[1];
        const distSq = dx * dx + dy * dy;

        if (distSq < minDistSq) {
          minDistSq = distSq;
          closestQuad = n;
          closestPoint = intersection;
          closestSide = [p1, p2];
        }
      }
    }
  }

  return [closestQuad, closestPoint, closestSide, minDistSq];
}

function reflectSegment(p0, p1, s0, s1) {
  // Direction vector of the normal of the mirror segment
  const dx = s1[1] - s0[1];
  const dy = s0[0] - s1[0];

  // Normalize direction vector
  const lenSq = dx * dx + dy * dy;
  if (lenSq === 0) throw new Error("s0 and s1 cannot be the same point");

  // Vector from p0 to p1
  const px = p1[0] - p0[0];
  const py = p1[1] - p0[1];

  // Project (px, py) onto the line (dx, dy)
  const dot = (px * dx + py * dy);
  const projX = (dot / lenSq) * dx;
  const projY = (dot / lenSq) * dy;

  // Reflect p0 across the projection point to get p2
  const p2x = p0[0] + 2 * (px - projX);
  const p2y = p0[1] + 2 * (py - projY);

  return [p2x, p2y];
}

function isInsideQuad(p, quad) {
  const EPS = 1e-5;
  if ((quad[0][0]+EPS < p[0] && p[0] < quad[2][0]-EPS) || (quad[2][0]+EPS < p[0] && p[0] < quad[0][0]-EPS)) {
    if ((quad[0][1]+EPS < p[1] && p[1] < quad[2][1]-EPS) || (quad[2][1]+EPS < p[1] && p[1] < quad[0][1]-EPS))
      return true;
  }
  return false;
}

function getQuadCenter(quad) {
  let [x0, y0] = quad[0];
  let [x1, y1] = quad[2];
  return [(x0 + x1)/2, (y0 + y1)/2];
}


function drawCursor() {
  if (selectedMirror != null)
    cursorSize = CURSOR_FACTOR;
  else if (getNearbyMirror() === null)
    cursorSize = 1.0
  else
    cursorSize = CURSOR_FACTOR;

  const ratio = cursorSize * 82 / 1920;
  const size = Math.round(canvas.width * ratio);
  const halfSize = Math.round(size / 2);

  let img = selectedMirror === null
    ? cursorImage
    : getTintedImage(cursorImage, "cyan");

  if (selectedMirror === null)
    ctx.drawImage(img, mouseX - halfSize, mouseY - halfSize, size, size);
  else {
    const [x0, y0] = rotatingMirrors[selectedMirror][0];
    const [x1, y1] = rotatingMirrors[selectedMirror][1];
    const cx = (x0 + x1)/2;
    const cy = (y0 + y1)/2;
    const [px, py] = gameToCanvas(cx, cy);
    ctx.drawImage(img, px - halfSize, py - halfSize, size, size);
  }
}

function drawTextAtGameCoord(text, x, y, options = {}) {
  const [px, py] = gameToCanvas(x, y);

  ctx.save();

  ctx.fillStyle = options.color || "purple";
  ctx.font = options.font || 'bold 42px "Courier New", monospace'; 
  ctx.textAlign = options.align || "center";
  ctx.textBaseline = options.baseline || "middle";

  ctx.fillText(text, px, py);

  ctx.restore();
}

async function loadAssets() {
  const res = await fetch('./levels.json');
  levelData = await res.json();

  // Load border image
  borderImage = await loadImage('sprites/border.png');

  // Load level images (0–13)
  const loadPromises = [];
  for (let i = 0; i < MAX_LEVELS; i++) {
    const lvlPromise = loadImage(`sprites/lvl${bgTextureMap[i]}.png`).then(img => {
      lvlImages[i] = img;
    });
    const bgPromise = loadImage(`sprites/lvl${bgTextureMap[i]}_bg.png`).then(img => {
      lvlBgImages[i] = img;
    });
    loadPromises.push(lvlPromise, bgPromise);
  }
  for (let i = 0; i < packetsN.length; i++) {
    const packetPromise = loadImage(`sprites/node_shatter_fg_${packetsN[i]}.png`).then(img => {
      packetsImages[i] = img;
    });
    loadPromises.push(packetPromise);
  }
  for (let i = 0; i < firewallsN.length; i++) {
    const firewallPromise = loadImage(`sprites/firewall_shatter_fg_${firewallsN[i]}.png`).then(img => {
      firewallsImages[i] = img;
    });
    loadPromises.push(firewallPromise);
  }
  const beamLayers = ["glow_tapered", "middle", "top"];
  for (let i = 0; i < beamLayers.length; i++) {
    const beamPromise = loadImage(`sprites/beam_${beamLayers[i]}.png`).then(img => {
      beamImages[i] = img;
    });
    loadPromises.push(beamPromise);
  }
  for (let i = 0; i < 4; i++) {
    const beamTipPromise = loadImage(`sprites/beam_spark_${i+1}.png`).then(img => {
      beamTipImages[i] = img;
    });
    loadPromises.push(beamTipPromise);
  }
  const mirrorLayers = ["base", "highlight"];
  for (let i = 0; i < mirrorLayers.length; i++) {
    const beamPromise = loadImage(`sprites/mirror_${mirrorLayers[i]}.png`).then(img => {
      mirrorImages[i] = img;
    });
    loadPromises.push(beamPromise);
  }
  const proxyLayers = [0, 1, 2, 3, 4, 5, 6, 7];
  for (let i = 0; i < proxyLayers.length; i++) {
    const beamPromise = loadImage(`sprites/prism_fg_${proxyLayers[i] * 45}.png`).then(img => {
      proxyImages[i] = img;
    });
    loadPromises.push(beamPromise);
  }

  await Promise.all(loadPromises);
}

function loadImage(src) {
  return new Promise((resolve) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.src = src;
  });
}

function getBgRenderBox() {
  const bgH = canvas.height;
  const scale = bgH / gameHeight;
  const bgW = gameWidth * scale * 1.2;
  const bgFinalH = bgH * 0.675;

  const bgX = (canvas.width - bgW) / 2;
  const bgY = (canvas.height - bgFinalH) / 2 + canvas.height * 0.0075;

  return {
    x: bgX,
    y: bgY,
    width: bgW,
    height: bgFinalH
  };
}

function canvasToGame(px, py) {
  const bgBox = getBgRenderBox();

  const minX = -0.1;
  const maxX = 1.1;
  const minY = 0.17;
  const maxY = 0.845;

  const nx = (px - bgBox.x) / bgBox.width;
  const ny = (py - bgBox.y) / bgBox.height;

  const x = minX + nx * (maxX - minX);
  const y = minY + ny * (maxY - minY);

  return [x, y];
}

function gameToCanvas(x, y) {
  const bgBox = getBgRenderBox();

  const minX = -0.1;
  const maxX = 1.1;
  const minY = 0.17;
  const maxY = 0.845;

  const nx = (x - minX) / (maxX - minX);
  const ny = (y - minY) / (maxY - minY);

  const px = bgBox.x + nx * bgBox.width;
  const py = bgBox.y + ny * bgBox.height;

  return [px, py];
}

function drawBoxImage(img, box, isLarge = false, angle = 0) {
  const boxSize = isLarge ? 128 : 64;
  
  // Get canvas-space coordinates of diagonal corners
  const [x0, y0] = gameToCanvas(box[0][0], box[0][1]);
  const [x1, y1] = gameToCanvas(box[2][0], box[2][1]);

  const centerX = (x0 + x1) / 2;
  const centerY = (y0 + y1) / 2;
  const boxW = Math.abs(x1 - x0);
  const boxH = Math.abs(y1 - y0);

  // Compute scale factors needed to stretch a 43×43 area to target box
  const scaleX = boxW / 43;
  const scaleY = boxH / 43;

  // The full image is 64x64, but we want to draw it so that its center (32,32)
  // scaled and aligned, puts the center 43x43 on the correct box.
  const drawW = boxSize * scaleX;
  const drawH = boxSize * scaleY;

  const drawX = centerX - (boxSize/2) * scaleX;
  const drawY = centerY - (boxSize/2) * scaleY;

  ctx.drawImage(img, drawX, drawY, drawW, drawH);
}

function drawPackets() {
  const packets = levelData[currentLevel]["vPackets"];

  for (let i = 0; i < levelData[currentLevel]["iMaxPackets"]; i++) {
    let n = 0;
    n = packetsN.findIndex(x => x >= packetDmgs[i]);
    if (n == -1)
      n = packetsImages.length - 1;
    if (n >= packetsImages.length)
      continue;
    drawBoxImage(packetsImages[n], packets[i], packetsN[n] > 60);
  }
}

function drawFirewalls() {
  const firewalls = levelData[currentLevel]["vFirewalls"];

  for (let i = 0; i < levelData[currentLevel]["iMaxFirewalls"]; i++) {
    let n = 0;
    n = firewallsN.findIndex(x => x >= firewallDmgs[i]);
    if (n == -1)
      n = packetsImages.length - 1;
    if (n >= firewallsImages.length)
      continue;
    drawBoxImage(firewallsImages[n], firewalls[i], firewallsN[n] > 60);
  }
}

function drawProxies() {
  const proxies = levelData[currentLevel]["vProxies"];

  for (let i = 0; i < levelData[currentLevel]["iMaxProxies"]; i++) {
    let n = Math.round(getSnappedProxyAngle()/45);
    drawBoxImage(proxyImages[n], proxies[i]);
  }
}

function getTintedImage(img, tintColor) {
  const offCanvas = document.createElement("canvas");
  offCanvas.width = img.width;
  offCanvas.height = img.height;
  const offCtx = offCanvas.getContext("2d");

  // Draw grayscale image
  offCtx.drawImage(img, 0, 0);

  // Apply tint
  offCtx.globalCompositeOperation = "source-in";
  offCtx.fillStyle = tintColor;
  offCtx.fillRect(0, 0, img.width, img.height);
  offCtx.globalCompositeOperation = "source-over";

  return offCanvas;
}

function drawBeam(p0, p1) {
  const [cx0, cy0] = gameToCanvas(p0[0], p0[1]);
  const [cx1, cy1] = gameToCanvas(p1[0], p1[1]);

  const dx = cx1 - cx0;
  const dy = cy1 - cy0;
  const angle = Math.atan2(dy, dx) - (Math.PI / 2);

  // Distance from p0 to p1 in canvas space (beam height)
  const beamLength = Math.sqrt(dx * dx + dy * dy);

  const drawW = 64 * canvas.height / 932;
  const drawH = beamLength;

  for (let img of beamImages) {
    const tinted = getTintedImage(img, beamColor);

    ctx.save();
    ctx.translate(cx1, cy1);                 // Move origin
    ctx.rotate(angle);                       // Rotate
    ctx.translate(-0.5 * drawW, -drawH);     // Align pixel (31, 0) to p1
    ctx.drawImage(tinted, 0, 0, drawW, drawH);
    ctx.restore();
  }
}

function drawBeamTip(p0, p1) {
  const [cx0, cy0] = gameToCanvas(p0[0], p0[1]);
  const [cx1, cy1] = gameToCanvas(p1[0], p1[1]);

  const dx = cx1 - cx0;
  const dy = cy1 - cy0;
  const angle = Math.atan2(dy, dx) + (Math.PI / 2);

  const drawW = 64;
  const drawH = 64;

  const img = beamTipImages[frameCount % beamTipImages.length];
  const tinted = getTintedImage(img, beamColor);

  ctx.save();
  ctx.translate(cx1, cy1);                 // Move origin
  ctx.rotate(angle);                       // Rotate
  ctx.translate(-0.5 * drawW, -(26/64) * drawH);
  ctx.drawImage(tinted, 0, 0, drawW, drawH);
  ctx.restore();
}

function drawOrientedImage(img, p1, p2) {
  const pmx = (p1[0] + p2[0]) / 2;
  const pmy = (p1[1] + p2[1]) / 2;
  const [cx, cy] = gameToCanvas(pmx, pmy);

  const dx = p2[0] - p1[0];
  const dy = p2[1] - p1[1];
  const angle = Math.atan2(dy, dx);

  // Grid cell dimensions (in canvas space)
  const cellWidth = canvas.width / 16;
  const cellHeight = canvas.height / 9;

  // Scale factors from original 64x64 image to target 54x54 in grid cell
  const scale = 64 / 54;
  const drawW = cellWidth / scale;
  const drawH = cellHeight / scale;

  ctx.save();
  ctx.translate(cx, cy);     // Move origin to center of image
  ctx.rotate(angle);         // Rotate around the center

  // Draw image with adjusted scaled dimensions and position
  ctx.drawImage(img, -drawW / 2, -drawH / 2, drawW, drawH);

  ctx.restore();
}

function drawMirrors(index) {
  for (let mirror of rotatingMirrors)
    drawOrientedImage(mirrorImages[index], mirror[0], mirror[1]);
}

function drawLevel() {
  const lvlImage = lvlImages[currentLevel];
  const lvlBgImage = lvlBgImages[currentLevel];
  
  gameWidth = lvlBgImage.width;
  gameHeight = lvlBgImage.height;

  const adjustedBorderHeight = borderImage.height / 1.778;
  const borderAspectRatio = borderImage.width / adjustedBorderHeight;

  let width = window.innerWidth;
  let height = window.innerHeight;

  if (width / height > borderAspectRatio) {
    width = height * borderAspectRatio;
  } else {
    height = width / borderAspectRatio;
  }

  canvas.width = width;
  canvas.height = height;
  ctx.clearRect(0, 0, width, height);

  // Get background render box
  const bgBox = getBgRenderBox();

  ctx.drawImage(lvlBgImage, bgBox.x, bgBox.y, bgBox.width, bgBox.height);
  drawMirrors(0);
  for (let i = 1; i < beams.length; i++)
    drawBeam(beams[i - 1], beams[i]);
  drawBeamTip(beams[beams.length - 2], beams[beams.length - 1]);
  drawMirrors(1);
  drawPackets();
  drawFirewalls();
  drawProxies();
  ctx.drawImage(lvlImage, 0, 0, canvas.width, canvas.height);
  
  // For debugging
  //const [cx, cy] = gameToCanvas(-0.1, (0.17+0.845)/2);
  //ctx.fillStyle = 'red';
  //ctx.beginPath();
  //ctx.arc(cx, cy, 5, 0, Math.PI * 2);
  //ctx.fill();
  
  ctx.drawImage(borderImage, 0, 0, canvas.width, canvas.height);
  drawTextAtGameCoord(formatTimeInterval(startTime, performance.now()), 0.85, 0.097);
  drawTextAtGameCoord(`L${currentLevel + 1}`, 1.095, 0.097);
}

function rotateMirror(mirrorIndex, degrees) {
  const mirror = rotatingMirrors[mirrorIndex];
  const p0 = mirror[0];
  const p1 = mirror[1];

  // Compute center point (midpoint between p0 and p1)
  const cx = (p0[0] + p1[0]) / 2;
  const cy = (p0[1] + p1[1]) / 2;

  const angle = Math.PI * degrees / 180;
  const cos = Math.cos(angle);
  const sin = Math.sin(angle);

  // Rotate p0
  let dx = p0[0] - cx;
  let dy = p0[1] - cy;
  mirror[0][0] = cx + dx * cos - dy * sin;
  mirror[0][1] = cy + dx * sin + dy * cos;

  // Rotate p1
  dx = p1[0] - cx;
  dy = p1[1] - cy;
  mirror[1][0] = cx + dx * cos - dy * sin;
  mirror[1][1] = cy + dx * sin + dy * cos;
}

function updateAngle(nFrames) {
  let angle = 0;
  let multiple = keys.Tab || keys.Space ? 2 : 1;
  let sign = keys.A ? -1 : 1;
  
  if (keys.A != keys.D && selectedMirror != null) {
    if (remainingAngle * sign < 0) {  // different signs -> finish rotation
      angle = multiple * nFrames;
      if (angle >= Math.abs(remainingAngle)) {
        angle = remainingAngle;
        remainingAngle = 0;
      }
      else {
        angle *= remainingAngle > 0 ? 1.0 : -1.0;
        remainingAngle -= angle;
      }
    }
    else {  // same sign, rotate normally
      angle = multiple * nFrames;
      if (angle >= Math.abs(remainingAngle)) {
        remainingAngle = 5 - ((angle - Math.abs(remainingAngle)) % 5);
      }
      else
        remainingAngle = Math.abs(remainingAngle) - angle;
      remainingAngle *= sign;
      angle *= sign;
    }
  }
  else {  // finish rotation
    angle = multiple * nFrames;
    if (angle >= Math.abs(remainingAngle)) {
      angle = remainingAngle;
      remainingAngle = 0;
    }
    else {
      angle *= remainingAngle > 0 ? 1.0 : -1.0;
      remainingAngle -= angle;
    }
  }
  
  if (lastSelectedMirror != null && angle != 0)
    rotateMirror(lastSelectedMirror, angle);
}

function getSnappedProxyAngle() {
  const ticks = Math.floor(proxyAngle/45);
  return 45 * (ticks % 8);
}

function redirectByProxy(point) {
  const angle = Math.PI * getSnappedProxyAngle() / 180;
  return [point[0] - Math.sin(angle), point[1] - Math.cos(angle)];
}

function updateLevel(nFrames) {
  if (nFrames == 0)
    return;
  
  updateAngle(nFrames);
  proxyAngle += nFrames * (45/25);  // 45 degrees every 25 frames
  let isProxyUsed = [];
  
  let quads = [];
  let quadLabel = [];
  
  quads.push(levelData[currentLevel]["vOuterWalls"]);
  quadLabel.push(["outerWall", null, 0]);
  
  for (let i = 0; i < levelData[currentLevel]["iMaxInnerWalls"]; i++) {
    quadLabel.push(["innerWall", i, quads.length]);
    quads.push(levelData[currentLevel]["vInnerWalls"][i]);
  }
  for (let i = 0; i < rotatingMirrors.length; i++) {
    quadLabel.push(["rotatingMirror", i, quads.length]);
    let mirror = rotatingMirrors[i];
    quads.push([mirror[0], mirror[0], mirror[1], mirror[1]]);
  }
  for (let i = 0; i < fixedMirrors.length; i++) {
    quadLabel.push(["fixedMirror", i, quads.length]);
    let mirror = fixedMirrors[i];
    quads.push([mirror[0], mirror[0], mirror[1], mirror[1]]);
  }
  for (let i = 0; i < levelData[currentLevel]["iMaxPackets"]; i++) {
    if (packetDmgs[i] > 60) {
      packetDmgs[i] += nFrames;
      continue;
    }
    quadLabel.push(["packet", i, quads.length]);
    quads.push(levelData[currentLevel]["vPackets"][i]);
  }
  for (let i = 0; i < levelData[currentLevel]["iMaxFirewalls"]; i++) {
    if (firewallDmgs[i] > 60) {
      firewallDmgs[i] += nFrames;
      continue;
    }
    quadLabel.push(["firewall", i, quads.length]);
    quads.push(levelData[currentLevel]["vFirewalls"][i]);
  }
  for (let i = 0; i < levelData[currentLevel]["iMaxProxies"]; i++) {
    quadLabel.push(["proxy", i, quads.length]);
    quads.push(levelData[currentLevel]["vProxies"][i]);
    isProxyUsed.push(false);
  }
  
  // Reconstruct beams
  let newStart = beams[0];
  let newEnd = beams[1];
  beams = [newStart];
  let continueBeam = true;
  beamColor = "cyan";
  while (continueBeam) {
    let mirror = null;
    let [n, point, side, dist] = findClosestRayIntersection(newStart, newEnd, quads);
    switch (quadLabel[n][0]) {
      case "outerWall":
        continueBeam = false;
        break;
      case "innerWall":
        continueBeam = false;
        break;
      case "rotatingMirror":
        mirror = rotatingMirrors[quadLabel[n][1]];
        newEnd = reflectSegment(newStart, point, mirror[0], mirror[1]);
        break;
      case "fixedMirror":
        mirror = fixedMirrors[quadLabel[n][1]];
        newEnd = reflectSegment(newStart, point, mirror[0], mirror[1]);
        break;
      case "packet":
        packetDmgs[quadLabel[n][1]] += nFrames;
        continueBeam = false;
        break;
      case "firewall":
        firewallDmgs[quadLabel[n][1]] += nFrames;
        continueBeam = false;
        beamColor = "red";
        break;
      case "proxy":
        if (isProxyUsed[quadLabel[n][1]])
          continueBeam = false;
        else {
          let center = getQuadCenter(quads[n]);
          if (isInsideQuad(newStart, quads[n]))
            isProxyUsed[quadLabel[n][1]] = true;
          else {
            beams.push(point);
            point = center;
          }
          newEnd = redirectByProxy(center);
        }
        break;
      default:
        // Error!
        continueBeam = false;
    }
    newStart = point;
    beams.push(newStart);
    if (beams.length > 30)
      continueBeam = false;
  }
}


function getNearbyMirror() {
  let dist2 = CURSOR_MAX_DIST2;
  let nearby = null;
  const [px, py] = canvasToGame(mouseX, mouseY);
  for (let i = 0; i < rotatingMirrors.length; i++){
    const [x0, y0] = rotatingMirrors[i][0];
    const [x1, y1] = rotatingMirrors[i][1];
    const cx = (x0 + x1)/2;
    const cy = (y0 + y1)/2;
    const dx = px - cx;
    const dy = py - cy;
    if (dx*dx + dy*dy < dist2) {
      nearby = i;
      dist2 = dx*dx + dy*dy;
    }
  }
  return nearby;
}


function initGame() {
  startButton.style.display = 'none';
  canvas.style.display = 'block';
  //currentLevel = 0;
  startFrameLoop();
}

function loadLevel() {
  beams = [];
  packetDmgs = [];
  firewallDmgs = [];
  rotatingMirrors = [];
  fixedMirrors = [];
  proxyAngle = 0;
  
  beamColor = "cyan";
  selectedMirror = null;
  lastSelectedMirror = null;
  remainingAngle = 0;
  cursorSize = 1.0;

  for (let p of levelData[currentLevel]["vBeam"])
    beams.push(p)
  for (let i = 0; i < levelData[currentLevel]["iMaxPackets"]; i++)
    packetDmgs.push(0);
  for (let i = 0; i < levelData[currentLevel]["iMaxFirewalls"]; i++)
    firewallDmgs.push(0);
  for (let i = 0; i < levelData[currentLevel]["iMaxNodes"]; i++) {
    if (i < levelData[currentLevel]["iMaxRotatingNodes"])
      rotatingMirrors.push(levelData[currentLevel]["vNodes"][i]);
    else
      fixedMirrors.push(levelData[currentLevel]["vNodes"][i]);
  }
}

function startFrameLoop() {
  function loop() {
    const elapsed = performance.now() - startTime;
    const nextFrame = Math.floor(elapsed / FRAME_TIME);
    
    if (nextFrame > frameCount) {
      updateLevel(nextFrame - frameCount);
      drawLevel();
      drawCursor();
      frameCount = nextFrame;
      
      let changeLevel = true;
      for (let dmg of packetDmgs) {
        if (dmg < 80) {
          changeLevel = false;
          break;
        }
      }
      if (changeLevel) {
        currentLevel = nextLevel;
        nextLevel = (currentLevel + 1) % MAX_LEVELS;
        loadLevel();
        drawLevel();
        drawCursor();
        startTime = performance.now();
        frameCount = 0;
      }
    }

    const timeToNext = FRAME_TIME - elapsed % FRAME_TIME;
    frameTimer = setTimeout(loop, timeToNext);
  }

  loadLevel();
  drawLevel();
  drawCursor();
  startTime = performance.now();
  frameCount = 0;
  loop();
}

// To stop the level
function stopFrameLoop() {
  clearTimeout(frameTimer);
}


loadAssets().then(() => {
  loading.style.display = "none";
  startButton.style.display = "block";
});

startButton.onclick = initGame;


window.addEventListener("resize", () => {
  if (canvas.style.display === "block") {
    drawLevel(0); // Redraw current level on resize
    drawCursor()();
  }
});

canvas.addEventListener("mousemove", (e) => {
  const rect = canvas.getBoundingClientRect();
  mouseX = e.clientX - rect.left;
  mouseY = e.clientY - rect.top;
});

canvas.addEventListener("mousedown", (e) => {
  if (e.button === 0) { // 0 = left button
    mouseDown = true;
    
    if (selectedMirror === null) {
      selectedMirror = getNearbyMirror();
      lastSelectedMirror = selectedMirror;
    }
    else {
      lastSelectedMirror = selectedMirror;
      selectedMirror = null;
    }
  }
});

canvas.addEventListener("mouseup", (e) => {
  if (e.button === 0) {
    mouseDown = false;
  }
});

window.addEventListener("keydown", (e) => {
  if (e.code === "KeyA") keys.A = true;
  if (e.code === "KeyD") keys.D = true;
  if (e.code === "Tab") {
    keys.Tab = true;
    e.preventDefault(); // prevent focus shift on Tab
  }
  if (e.code === "Space") keys.Space = true;
  if ((e.key === "Enter" || e.code === "Space") && startButton.style.display !== "none") {
    startButton.click(); // Simulate button click
  }
});

window.addEventListener("keyup", (e) => {
  if (e.code === "KeyA") keys.A = false;
  if (e.code === "KeyD") keys.D = false;
  if (e.code === "Tab") keys.Tab = false;
  if (e.code === "Space") keys.Space = false;
  if (e.code === "PageUp") {
    // Destroy all packets and go back 1 level
    for (let i = 0; i < packetDmgs.length; i++) packetDmgs[i] = 80;
    nextLevel = (currentLevel + MAX_LEVELS - 1) % MAX_LEVELS;
  }
  if (e.code === "PageDown") {
    // Destroy all packets and go forward 1 level
    for (let i = 0; i < packetDmgs.length; i++) packetDmgs[i] = 80;
    nextLevel = (currentLevel + 1) % MAX_LEVELS;
  }
});

window.addEventListener("blur", () => {
  keys.A = false;
  keys.D = false;
  keys.Tab = false;
  mouseDown = false;
});
