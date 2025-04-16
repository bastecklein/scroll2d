import { hexToRGB, distBetweenPoints, removeFromArray, guid } from "common-helpers";
import { handleInput, clearElementForTouch } from "input-helper";
import particles2 from "particles2";

window.addEventListener("resize", globalResize);

const π = Math.PI;
const TWO_π = π * 2;
const ONE_EIGHTY_π = π / 180;
const PIXEL_STEP  = 10;
const LINE_HEIGHT = 40;
const PAGE_HEIGHT = 800;
const MIN_LERP = 0.001;
const SEGMENTED_RENDER_BUFFER = 1;
const TARGET_DELTA = 1000 / 60;

let engineInstances = {};

let usedRenderObjects = [];
let usedPopperObjects = [];
let lightInstructionRecycling = [];

let lastRAF = null;
let currentFPS = 0;

export function getInstance(options) {
    const engine = new Scroll2dEngine(options);
    engineInstances[engine.id] = engine;
    return engine;
}

export class Scroll2dEngine {
    constructor(options) {

        const instance = this;

        this.id = guid();

        this.scale = options.scale || window.devicePixelRatio || 1;

        this.autoScale = true;

        if(options.scale) {
            this.autoScale = false;
        }

        this.lastScale = this.scale;

        this.drawQueue = [];
        this.aboveFoldDrawQueue = [];
        this.textPoppers = [];
        this.lightBlockers = [];
        this.lightSources = [];

        this.selectionColor = options.selectionColor || "#4CAF50";

        this.running = false;
        this.changed = true;
        this.staticCallMade = false;
        this.isometricMode = options.isometricMode || false;
        this.fitGridToHeight = options.fitGridToHeight || false;
        this.staticMapInit = false;
        this.didAMove = false;
        this.didMove = false;
        this.isDown = false;
        this.isHold = false;
        this.usingTouch = false;
        this.isSelection = false;
        this.nextDownSelection = false;
        this.usingMouse = false;
        this.isPainting = false;
        this.isPinching = false;
        this.instructionsRecieved = false;
        this.doubleHeightTiles = options.doubleHeightTiles || false;
        this.useFastRenderMode = options.fastRenderMode || false;
        this.pixelated = options.pixelated || false;

        this.fullMapRenderCallback = null;

        this.colorFilter = null;
        this.filterAmount = 0;
        this.darknessMaskColor = null;

        this.viewX = 0;
        this.viewY = 0;

        this.actualX = 0;
        this.actualY = 0;

        this.startX = 0;
        this.startY = 0;

        this.holdX = 0;
        this.holdY = 0;

        this.curX = 0;
        this.curY = 0;

        this.selectionX = 0;
        this.selectionY = 0;

        this.selectionTopX = 0;
        this.selectionTopY = 0;

        this.selectionWidth = 0;
        this.selectionHeight = 0;

        this.lastHoverX = 0;
        this.lastHoverY = 0;

        this.lastPaintX = 0;
        this.lastPaintY = 0;

        this.lerpX = 0;
        this.lerpY = 0;

        this.lerpCallback = null;
        this.lerpSpeed = 0.15;
        this.lerpAccuracy = 1;

        this.viewPadding = 0;

        this.zoomLevel = 1.0;

        this.fpsLimiter = options.fpsLimiter || 1;
        this.fpsCounter = 0;

        this.maxZoom = options.maxZoom || 3.0;
        this.minZoom = options.minZoom || 0.1;

        this.width = 0;
        this.height = 0;

        this.winWidth = 0;
        this.winHeight = 0;

        this.mapWidth = -1;
        this.mapHeight = -1;

        this.mapTotalWidth = -1;
        this.mapTotalHeight = -1;

        this.gridSize = options.gridSize || 40;
        this.relativeGridSize = this.gridSize;
        this.halfGridSize = this.gridSize / 2;
        this.halfRelativeGridSize = this.relativeGridSize / 2;
        this.quarterRelativeGridSize = this.relativeGridSize / 4;
        this.twentiethGridSize = this.relativeGridSize / 20;

        this.renderOrder = 0;

        this.staticMaxZIndex = 1;

        this.lastDistance = null;

        this.pointerListener = options.onPointer || null;
        this.holdFunction = options.onHold || null;
        this.selectionFunction = options.onSelection || null;
        this.selectionProgressFunction = options.onSelectionProgress || null;
        this.hoverFunction = options.onHover || null;
        this.paintFunction = options.onPaint || null;
        this.viewportChangeFunction = options.onViewportChange || null;
        this.releaseFunction = options.onRelease || null;
        this.clickFunction = options.onClick || null;
        this.rightClickFunction = options.onRightClick || null;
        this.drawFunction = options.onDraw || null;
        this.updateFunction = options.onUpdate || null;

        this.paintTimer = null;
        this.paintTimeoutFunction = null;

        this.screenshotCanvas = null;
        this.screenshotContext = null;
        this.screenshotCallback = null;
        this.screenshotPhase = false;

        this.particleEngine = null;

        this.holdTimer = null;

        this.staticMap = {};

        this.limits = {
            xMin: 0,
            xLimit: 0,
            yMin: 0,
            yLimit: 0
        };

        this.mouseScrolling = {
            up: false,
            down: false,
            left: false,
            right: false
        };

        this.padScrolling = {
            up: false,
            down: false,
            left: false,
            right: false
        };

        this.padRightScrolling = {
            up: false,
            down: false,
            left: false,
            right: false
        };

        this.padTriggers = {
            left: false,
            right: false
        };

        this.aDownTime = 0;

        this.pointers = {};
        this.primaryPointer = null;
        this.pointersDown = 0;

        const logicFPS = options.logicFPS || 60;
        this.updateTime = 1000 / logicFPS;
        this.lastUpdateUpdate = 0;

        this.gamepadNegotiationTimer = 0;

        this.viewBounds = null;

        this.holder = null;

        if(options.holder) {
            this.holder = options.holder;
        } else {
            this.holder = document.createElement("div");
            this.holder.classList.add("scroll2d-holder");
            absoluteAndFillElement(this.holder);
            document.body.appendChild(this.holder);
        }

        this.lightCanvas = document.createElement("canvas");
        this.lightFinalRenderCanvas = document.createElement("canvas");
        this.staticCanvas = document.createElement("canvas");
        this.preRenderCanvas = document.createElement("canvas");
        this.gradientFilterCanvas = document.createElement("canvas");

        this.canvas = document.createElement("canvas");
        this.filterOverlay = document.createElement("div");

        this.context = this.canvas.getContext("2d");
        this.staticContext = this.staticCanvas.getContext("2d");
        this.lightContext = this.lightCanvas.getContext("2d");
        this.lightFinalRenderContext = this.lightFinalRenderCanvas.getContext("2d");
        this.preRenderContext = this.preRenderCanvas.getContext("2d");
        this.gradientFilterContext = this.gradientFilterCanvas.getContext("2d");

        if(this.pixelated) {
            pixelateCanvas(this.canvas);
            pixelateCanvas(this.staticCanvas);
            pixelateCanvas(this.lightCanvas);
            pixelateCanvas(this.lightFinalRenderCanvas);
            pixelateCanvas(this.preRenderCanvas);
            pixelateCanvas(this.gradientFilterCanvas);
        }

        this.holder.appendChild(this.canvas);
        this.holder.appendChild(this.filterOverlay);

        clearElementForTouch(this.canvas);

        handleInput({
            element: instance.filterOverlay,
            down: function(e) {
                onInstanceDown(instance, e);
            },
            move: function(e) {
                onInstanceMove(instance, e);
            },
            up: function(e) {
                onInstanceUp(instance, e);
            }
        });

        this.filterOverlay.addEventListener("wheel", function(e) {
            e.preventDefault();
            onInstanceWheel(instance, e);
        });

        absoluteAndFillElement(this.canvas);
        absoluteAndFillElement(this.filterOverlay);

        this.normalizeFilterOverlaySize();
        this.gamepadAllStop();

        setTimeout(function() {
            instance.running = true;
            instance.resize();
        }, 200);
    }

    destroy() {
        this.running = false;
        this.holder.innerHTML = "";
        delete engineInstances[this.id];
    }

    render(delta) {
        renderScrollInstance(this, delta);
    }

    resize() {
        resizeInstance(this);
    }

    setMapDimensions(width, height) {
        this.mapWidth = width;
        this.mapHeight = height;

        if(width == null || height == null || width < 0 || height < 0) {
            this.mapWidth = -1;
            this.mapHeight = -1;

            this.mapTotalWidth = -1;
            this.mapTotalHeight = -1;

            this.setLimits();
            return;
        }

        this.mapTotalWidth = this.mapWidth * this.relativeGridSize;
        this.mapTotalHeight = this.mapHeight * this.relativeGridSize;

        this.setLimits();

        this.drawQueue = [];
        this.aboveFoldDrawQueue = [];

        if(this.staticCallMade) {
            this.initStaticMap();
        }

        this.changed = true;
    }

    setLimits() {
        if(this.mapWidth > 0 && this.mapHeight > 0) {
            if(this.isometricMode) {
                this.limits.xMin = -(this.mapTotalWidth / 2) - this.relativeGridSize;
                this.limits.xLimit = (this.mapTotalWidth / 2) - this.winWidth + (this.relativeGridSize * 2);

                this.limits.yMin = -this.relativeGridSize;
                this.limits.yLimit = (this.mapTotalHeight / 2) - this.winHeight + (this.relativeGridSize * 2);
            } else {
                this.limits.xMin = 0 - (this.winWidth / 2);
                this.limits.xLimit = this.mapTotalWidth - (this.winWidth / 2);

                this.limits.yMin = 0 - (this.winHeight / 2);
                this.limits.yLimit = this.mapTotalHeight - (this.winHeight / 2);

                if(this.fitGridToHeight) {
                    this.limits.yMin = 0;
                    this.limits.yLimit = 0;
                }
            }
        } else {
            this.limits.xMin = -99999999;
            this.limits.xLimit = 99999999;
            this.limits.yMin = -99999999;
            this.limits.yLimit = 99999999;
        }
    }

    setRelativeGridSize() {
        this.relativeGridSize = Math.round(this.gridSize * this.zoomLevel);

        if(this.relativeGridSize % 2 !== 0) {
            this.relativeGridSize++;
        }

        this.halfGridSize = this.gridSize / 2;

        this.halfRelativeGridSize = this.relativeGridSize / 2;
        this.quarterRelativeGridSize = this.relativeGridSize / 4;
        this.twentiethGridSize = this.relativeGridSize / 20;
    }

    setViewBounds() {
        const min = this.positionToCoords(0 - this.viewPadding, 0 - this.viewPadding);
        const max = this.positionToCoords(this.winWidth + this.viewPadding, this.winHeight + this.viewPadding);

        if(this.isometricMode) {
            const tr = this.positionToCoords(this.winWidth + this.viewPadding, 0 - this.viewPadding);
            const bl = this.positionToCoords(0 - this.viewPadding, this.winHeight + this.viewPadding);

            this.viewBounds = new ViewBounds(min.x, tr.y, max.x, bl.y, this);
        } else {
            this.viewBounds = new ViewBounds(min.x, min.y, max.x, max.y, this);
        }
    }

    getViewBounds() {
        if(this.viewBounds == null) {
            this.setViewBounds();
        }

        return this.viewBounds;
    }

    initStaticMap() {
        this.staticMap = {};
        this.staticMapInit = true;
    }

    positionToCoords(x, y) {
        return new Coord(x, y, this);
    }

    getPointer(id, x, y, type) {
        if(this.pointers[id]) {
            return this.pointers[id];
        }

        const pointer = {
            x: x,
            y: y,
            lastX: x,
            lastY: y,
            origX: x,
            origY: y,
            primary: false,
            type: type,
            rightClick: false,
            down: false
        };

        if(this.pointersDown === 0) {
            pointer.primary = true;
            this.primaryPointer = pointer;
        }

        this.pointers[id] = pointer;

        return pointer;
    }

    setSelectionPoints(x, y) {
        if(x < this.selectionX) {
            this.selectionTopX = x;
            this.selectionWidth = this.selectionX - x;
        } else {
            this.selectionTopX = this.selectionX;
            this.selectionWidth = x - this.selectionX;
        }

        if(y < this.selectionY) {
            this.selectionTopY = y;
            this.selectionHeight = this.selectionY - y;
        } else {
            this.selectionTopY = this.selectionY;
            this.selectionHeight = y - this.selectionY;
        }
    }

    sendSelectionPointsToFunction(func) {
        const rx = this.selectionTopX + this.selectionWidth;
        const by = this.selectionTopY + this.selectionHeight;

        const tl = this.getCoordAndActual(this.selectionTopX, this.selectionTopY);
        const tr = this.getCoordAndActual(rx, this.selectionTopY);
        const bl = this.getCoordAndActual(this.selectionTopX, by);
        const br = this.getCoordAndActual(rx, by);

        func(tl, tr, bl, br);
    }

    getCoordAndActual(x, y) {
        const result = {
            aX: x,
            aY: y,
            x: x,
            y: y
        };

        const position = this.positionToCoords(x, y);

        result.x = position.x;
        result.y = position.y;

        return result;
    }

    checkBounds() {
        if(this.viewX < this.limits.xMin) {
            this.viewX = this.limits.xMin;
        }

        if(this.viewX > this.limits.xLimit) {
            this.viewX = this.limits.xLimit;
        }

        if(this.viewY < this.limits.yMin) {
            this.viewY = this.limits.yMin;
        }

        if(this.viewY > this.limits.yLimit) {
            this.viewY = this.limits.yLimit;
        }

        this.setViewBounds();
    }

    notifyViewportChange(wasManual = false) {
        if(this.viewportChangeFunction) {
            this.viewportChangeFunction(wasManual);
        }
    }

    doZoom(zoomIn, amt) {
        let lvl = this.zoomLevel;

        if (amt) {
            if (amt > 0.15) {
                amt = 0.15;
            }
            if (amt < -0.15) {
                amt = -0.15;
            }
            if (zoomIn) {
                if (lvl < this.maxZoom) {
                    lvl -= (lvl * amt);
                }
            } else {
                if (lvl > this.minZoom) {
                    lvl -= (lvl * amt);
                }
            }
        } else {
            if (zoomIn) {
                if (lvl < this.maxZoom) {
                    lvl += 0.15;
                }
            } else {
                if (lvl > this.minZoom) {
                    lvl -= 0.15;
                }
            }
        }
        
        this.setZoomLevel(lvl);
    }

    setZoomLevel(level) {
        const position = this.getCenterPosition();

        this.zoomLevel = level;

        if(this.zoomLevel >= 0.9 && this.zoomLevel <= 1.1) {
            this.zoomLevel = 1;
        }

        if(this.zoomLevel > this.maxZoom) {
            this.zoomLevel = this.maxZoom;
        }

        if(this.zoomLevel < this.minZoom) {
            this.zoomLevel = this.minZoom;
        }

        this.setRelativeGridSize();

        this.instructionsRecieved = true;
        this.changed = true;

        this.forceSceneChange();

        this.centerOnCoord(position.x, position.y);

        this.notifyViewportChange(true);
    }

    getCenterPosition() {
        return this.positionToCoords(this.winWidth / 2, this.winHeight / 2);
    }

    forceSceneChange() {
        this.setMapDimensions(this.mapWidth, this.mapHeight);
        this.initStaticMap();
        this.setRelativeGridSize();
        this.notifyViewportChange(true);

        this.changed = true;
    }

    centerOnCoord(x, y, exactLocation = false) {

        if(exactLocation) {
            this.viewX = x - (this.winWidth / 2);
            this.viewY = y - (this.winHeight / 2);
        } else {
            this.lastHoverX = x;
            this.lastHoverY = y;

            if(this.isometricMode) {
                this.viewX = ((x - y) * this.halfRelativeGridSize - (this.winWidth / 2));
                this.viewY = ((x + y) * this.quarterRelativeGridSize - (this.winHeight / 2));
            } else {
                this.viewX = Math.floor(((x * this.relativeGridSize) + this.halfRelativeGridSize) - (this.winWidth / 2));
                this.viewY = Math.floor(((y * this.relativeGridSize) + this.halfRelativeGridSize) - (this.winHeight / 2));
            }
        }

        if(this.fitGridToHeight) {
            this.viewY = 0;
        }

        this.checkBounds();
        this.changed = true;
    }

    getStaticItem(x, y, z) {
        if(!this.staticMapInit) {
            return null;
        }

        if(!this.staticMap[z]) {
            this.staticMap[z] = {};
        }

        if(!this.staticMap[z][x]) {
            this.staticMap[z][x] = {};
        }

        if(this.staticMap[z][x][y]) {
            return this.staticMap[z][x][y];
        }

        return null;
    }

    setStaticItem(x, y, z, item) {
        if(!this.staticMapInit) {
            return null;
        }

        if(!this.staticMap[z]) {
            this.staticMap[z] = {};
        }

        if(!this.staticMap[z][x]) {
            this.staticMap[z][x] = {};
        }

        this.staticMap[z][x][y] = item;
    }

    setNextDownInSelection(val) {
        this.nextDownSelection = val;
    }

    drawStaticTile(img, x, y, zIndex) {
        doDrawStaticTile(this, img, x, y, zIndex);
    }

    drawTile(img, x, y, zIndex, blocksLight, alpha) {
        return doDrawTile(this, img, x, y, zIndex, blocksLight, alpha);
    }

    drawSprite(img, x, y, tX = x, tY = y, step = 0, meterPercent = null, meterColor = "#ff0000", alpha = 1, zIndex = 0, tileWidth = 1, tileHeight = 1, chevrons = null, angle = 0, centerChevrons = false, textLabel = null, yOffset = 0, scale = 1, textSize = 20, textFont = null, textYOffset = 0, meterYOffset = 0, elevation = 0) {
        return doDrawSprite(this, img, x, y, tX, tY, step, meterPercent, meterColor, alpha, zIndex, tileWidth, tileHeight, chevrons, angle, centerChevrons, textLabel, yOffset, scale, textSize, textFont, textYOffset, meterYOffset, elevation);
    }

    drawSpriteWithOptions(options) {
        const img = options.img || null;
        const x = options.x || 0;
        const y = options.y || 0;
        const tX = options.tX || x;
        const tY = options.tY || y;
        const step = options.step || 0;
        const meterPercent = options.meterPercent || null;
        const meterColor = options.meterColor || "#ff0000";
        const alpha = options.alpha || 1;
        const zIndex = options.zIndex || 0;
        const tileWidth = options.tileWidth || 1;
        const tileHeight = options.tileHeight || 1;
        const chevrons = options.chevrons || null;
        const angle = options.angle || 0;
        const centerChevrons = options.centerChevrons || false;
        const textLabel = options.textLabel || null;
        const yOffset = options.yOffset || 0;
        const scale = options.scale || 1;
        const textSize = options.textSize || 20;
        const textFont = options.textFont || null;
        const textYOffset = options.textYOffset || 0;
        const meterYOffset = options.meterYOffset || 0;
        const elevation = options.elevation || 0;

        return doDrawSprite(this, img, x, y, tX, tY, step, meterPercent, meterColor, alpha, zIndex, tileWidth, tileHeight, chevrons, angle, centerChevrons, textLabel, yOffset, scale, textSize, textFont, textYOffset, meterYOffset, elevation);
    }

    checkVisibility(x, y) {
        let dx, dy;

        if(this.isometricMode) {
            dx = (x - y) * this.halfRelativeGridSize;
            dy = (x + y) * this.quarterRelativeGridSize;
        } else {
            dx = x * this.relativeGridSize;
            dy = y * this.relativeGridSize;
        }

        const rgPad = this.relativeGridSize + this.viewPadding;

        if(dx > this.viewX - rgPad && dx < this.winWidth + this.viewX + rgPad && dy > this.viewY - rgPad && dy < this.winHeight + this.viewY + rgPad) {
            return true;
        }

        return false;
    }

    lerpToCoord(x, y, callback, speed = 0.15, accuracy = 1) {
        this.lerpX = x;
        this.lerpY = y;
        this.lerpCallback = callback;
        this.lerpSpeed = speed;
        this.lerpAccuracy = accuracy;
    }

    setViewPadding(padding) {
        this.viewPadding = padding;
    }

    setGridSize(size) {
        const position = this.getCenterPosition();

        this.gridSize = size;
        this.setRelativeGridSize();
        this.changed = true;
        resizeInstance(this);

        this.centerOnCoord(position.x, position.y);
    }

    setDoubleHeightTiles(val) {
        this.doubleHeightTiles = val;
    }

    setDrawFunction(func) {
        this.drawFunction = func;
    }

    setClickFunction(func) {
        this.clickFunction = func;
    }

    setPointerListener(func) {
        this.pointerListener = func;
    }

    setRightClickFunction(func) {
        this.rightClickFunction = func;
    }

    setViewportChangeFunction(func) {
        this.viewportChangeFunction = func;
    }

    setHoverFunction(func) {
        this.hoverFunction = func;
    }

    setHoldFunction(func) {
        this.holdFunction = func;
    }

    setReleaseFunction(func) {
        this.releaseFunction = func;
    }

    setPaintFunction(func) {
        this.paintFunction = func;
    }

    setSelectionFunction(func, progress, color) {
        this.selectionFunction = func;
        this.selectionProgressFunction = progress;
        this.selectionColor = color;
    }

    alertPainting(callback = null, timeout = 600) {
        this.isPainting = true;

        this.paintTimeoutFunction = callback;

        if(this.paintTimer) {
            clearTimeout(this.paintTimer);
        }

        const engine = this;

        this.paintTimer = setTimeout(function() {
            engine.clearOutPaint();
        }, timeout);
    }

    clearOutPaint(noCallback = false) {
        this.isPainting = false;

        if(this.paintTimer) {
            clearTimeout(this.paintTimer);
        }
    
        this.paintTimer = null;
    
        if(noCallback) {
            return;
        }
    
        if(this.paintTimeoutFunction) {
            this.paintTimeoutFunction();
        }
    }

    popText(x, y, text, color = "#FF0000") {
        doPopText(this, x, y, text, color);
    }

    drawSquare(color, x, y, zIndex = 0, composite = null) {
        doDrawSquare(this, color, x, y, zIndex, composite);
    }

    drawText(text, x, y, color = "#ffffff", stroke = "#000000", size = 20, font = null, zIndex = 1) {
        doDrawText(this, text, x, y, color, stroke, size, font, zIndex);
    }

    setSnowing(val) {
        if(this.particleEngine) {
            this.particleEngine.rainRunning = val;
        }
    }

    setEmbers(val) {
        if(this.particleEngine) {
            this.particleEngine.embersRunning = val;
        }
    }

    setRaining(val) {
        if(this.particleEngine) {
            this.particleEngine.rainRunning = val;
        }
    }

    renderFullMap(callback) {
        this.setZoomLevel(1);
        this.fullMapRenderCallback = callback;
    }

    setIsometric(val) {
        this.isometricMode = val;
        this.changed = true;
    }

    getFPS() {
        return currentFPS;
    }

    setUpdateFunction(func, targetFPS = 60) {
        this.updateFunction = func;
        this.updateTime = 1000 / targetFPS;
    }

    update(timestamp, delta) {
        processUpdate(this, timestamp, delta);
    }

    setFitGridToHeight(val) {
        this.fitGridToHeight = val;
        resizeInstance(this);
    }

    setColorFilter(color = null, amount = 0.1) {
        this.darknessMaskColor = null;
        this.colorFilter = color;
        this.filterAmount = amount;
        this.changed = true;
    }

    initParticleEngine() {
        this.particleEngine = particles2.getInstance();
    }

    playParticleEffect(effect, x, y) {
        if(!this.particleEngine) {
            return;
        }

        let px, py;

        if(this.isometricMode) {
            px = (x - y) * this.halfRelativeGridSize;
            py = (x + y) * this.quarterRelativeGridSize;
        } else {
            px = x * this.relativeGridSize; 
            py = y * this.relativeGridSize;
        }

        const useX = px - this.viewX;
        const useY = py - this.viewY;

        this.particleEngine.playEffect(effect, useX, useY);
    }

    drawLine(color, x, y, x2, y2, zIndex = 0, centerInTile = false, lineWidth = 1, dashed = false) {
        doDrawLine(this, color, x, y, x2, y2, zIndex, centerInTile, lineWidth, dashed);
    }

    drawCircle(color, x, y, tileRadius, zIndex = 0, lineWidth = 1, dashed = false) {
        doDrawCircle(this, color, x, y, tileRadius, zIndex, lineWidth, dashed);
    }

    setBorderColor(color) {
        if(color) {
            this.style.border = "4px solid " + color;
            this.filterOverlay.style.top = "0px";
            this.filterOverlay.style.left = "0px";
            this.filterOverlay.style.width = "calc(100% - 8px)";
            this.filterOverlay.style.height = "calc(100% - 8px)";
        } else {
            this.filterOverlay.style.border = "none";
            this.normalizeFilterOverlaySize();
        }
    }

    normalizeFilterOverlaySize() {
        this.filterOverlay.style.top = "0px";
        this.filterOverlay.style.left = "0px";
        this.filterOverlay.style.width = "100%";
        this.filterOverlay.style.height = "100%";
    }

    outlineTileGroup(tilesArray, zIndex, color, lineWidth, dashed, tileOffset = 0) {
        const linesToDraw = getGroupRegionLines(tilesArray);

        for(const line of linesToDraw) {
            this.drawLine(color, line.x1 - tileOffset, line.y1 - tileOffset, line.x2 + tileOffset, line.y2 + tileOffset, zIndex, false, lineWidth, dashed);
        }
    }

    setFastRenderMode(val) {
        this.useFastRenderMode = val;
    }

    getZoomLevel() {
        return this.zoomLevel;
    }

    setMaxZoomLevel(val) {
        this.maxZoom = val;
    }

    setMinZoomLevel(val) {
        this.minZoom = val;
    }

    startPan(direction) {
        this.mouseScrolling[direction] = true;
    }

    endPan(direction) {
        this.mouseScrolling[direction] = false;
    }

    takeScreenshot(callback) {
        this.screenshotCanvas = document.createElement("canvas");
        this.screenshotContext = this.screenshotCanvas.getContext("2d");

        if(this.pixelated) {
            pixelateCanvas(this.screenshotCanvas);
        }

        this.screenshotCanvas.width = this.width;
        this.screenshotCanvas.height = this.height;

        this.screenshotCallback = callback;
        this.screenshotPhase = true;
    }

    setFPSLimiter(val) {
        this.fpsLimiter = val;
    }

    modifyViewX(amount) {
        this.viewX += amount;
        this.checkBounds();
        this.changed = true;
        this.notifyViewportChange();
    }

    modifyViewY(amount) {
        this.viewY += amount;
        this.checkBounds();
        this.changed = true;
        this.notifyViewportChange();
    }

    getUsingTouch() {
        return this.usingTouch;
    }

    gamepadDown(button) {
        onGamepadDown(this, button);
    }

    gamepadUp(button) {
        onGamepadUp(this, button);
    }

    drawLight(x, y, radius = this.relativeGridSize, color = "#ffffff", tX = x, tY = y, step = 0, intensity = 0.2) {
        doDrawLight(this, x, y, radius, color, tX, tY, step, intensity);
    }

    gamepadAllStop() {
        for(const button in this.padScrolling) {
            this.padScrolling[button] = false;
        }

        for(const button in this.padRightScrolling) {
            this.padRightScrolling[button] = false;
        }

        for(const button in this.padTriggers) {
            this.padTriggers[button] = false;
        }

        this.aDownTime = 0;
    }

    getCanvasStream(fps = 25) {
        return this.canvas.captureStream(fps);
    }

    getDrawCanvas() {
        return this.canvas;
    }
}

class Coord {
    constructor(x, y, instance) {
        this.x = x;
        this.y = y;

        this.px = x;
        this.py = y;

        if(instance) {
            if(instance.isometricMode) {
                this.px = ((x + instance.viewX) / instance.halfRelativeGridSize + (y + instance.viewY) / instance.quarterRelativeGridSize) / 2;
                this.py = ((y + instance.viewY) / instance.quarterRelativeGridSize - (x + instance.viewX) / instance.halfRelativeGridSize) / 2;
            } else {
                this.px = (x + instance.viewX) / instance.relativeGridSize;
                this.py = (y + instance.viewY) / instance.relativeGridSize;
            }
        }

        this.x = Math.floor(this.px);
        this.y = Math.floor(this.py);
    }
}

class ViewBounds {
    constructor(minX, minY, maxX, maxY, instance) {
        this.minX = minX;
        this.minY = minY;
        this.maxX = maxX;
        this.maxY = maxY;

        if(instance && instance.mapWidth > 0 && instance.mapHeight > 0) {
            if(this.minX < 0) {
                this.minX = 0;
            }

            if(this.minY < 0) {
                this.minY = 0;
            }

            if(this.maxX > instance.mapWidth) {
                this.maxX = instance.mapWidth;
            }

            if(this.maxY > instance.mapHeight) {
                this.maxY = instance.mapHeight;
            }
        }
    }
}

class RenderItem {
    constructor() {
        this.x = 0;
        this.y = 0;
        this.img = null;
        this.w = 0;
        this.h = 0;
        this.alpha = null;
        this.isBar = false;
        this.barWidth = 0;
        this.meterWidth = 0;
        this.barColor = "#000000";
        this.isSquare = false;
        this.isLine = false;
        this.isCircle = false;
        this.color = "#000000";
        this.nearness = 0;
        this.tileWidth = 1;
        this.tileHeight = 1;
        this.zIndex = 0;
        this.altitude = 0;
        this.segmentX = -1;
        this.cX = 0;
        this.cY = 0;
        this.destSegX = 0;
        this.sW = 0;
        this.sH = 0;
        this.blocksLight = false;
        this.ro = 0;
        this.lineWidth = 1;
        this.angle = 0;
        this.tX = 0;
        this.tY = 0;
        this.dashedLine = false;
        this.isText = null;
        this.textFont = null;
    }
}

export class Chevron {
    constructor(color = null, image = null) {
        this.color = color;
        this.image = image;
    }
}

class TextPopItem {
    constructor(x, y, text, color) {
        this.x = x;
        this.y = y;
        this.text = text;
        this.color = color;
        this.alpha = 1.0;
        this.cashed = false;
    }
}

class LightInstruction {
    constructor(x, y, radius, color, intensity) {
        this.x = x;
        this.y = y;
        this.radius = radius;
        this.color = color;
        this.intensity = intensity;
    }
}

export function globalResize() {
    for(const id in engineInstances) {
        const engine = engineInstances[id];
        engine.resize();
    }
}

export function hexToRgb(hex) {
    return hexToRGB(hex);
}

function resizeInstance(engine) {
    if(!engine.canvas) {
        return;
    }

    engine.changed = true;

    engine.winWidth = engine.holder.offsetWidth;
    engine.winHeight = engine.holder.offsetHeight;

    engine.width = Math.round(engine.winWidth * engine.scale);
    engine.height = Math.round(engine.winHeight * engine.scale);

    engine.canvas.width = engine.width;
    engine.canvas.height = engine.height;

    engine.staticCanvas.width = engine.width;
    engine.staticCanvas.height = engine.height;

    engine.lightCanvas.width = engine.width;
    engine.lightCanvas.height = engine.height;

    engine.lightFinalRenderCanvas.width = engine.width;
    engine.lightFinalRenderCanvas.height = engine.height;

    if(engine.fitGridToHeight && engine.mapHeight > 0) {
        engine.gridSize = engine.winHeight / engine.mapHeight;
    }

    engine.context.setTransform(1, 0, 0, 1, 0, 0);
    engine.context.scale(engine.scale, engine.scale);

    engine.staticContext.setTransform(1, 0, 0, 1, 0, 0);
    engine.staticContext.scale(engine.scale, engine.scale);

    engine.lightContext.setTransform(1, 0, 0, 1, 0, 0);
    engine.lightContext.scale(engine.scale, engine.scale);

    engine.lightFinalRenderContext.setTransform(1, 0, 0, 1, 0, 0);
    engine.lightFinalRenderContext.scale(engine.scale, engine.scale);

    engine.setRelativeGridSize();

    engine.mapTotalWidth = engine.mapWidth * engine.relativeGridSize;
    engine.mapTotalHeight = engine.mapHeight * engine.relativeGridSize;

    engine.setLimits();
    engine.setViewBounds();

    engine.changed = true;
}

function globalRender(t) {
    requestAnimationFrame(globalRender);
    
    if(lastRAF == null) {
        lastRAF = t;
    }

    const elapsed = t - lastRAF;
    lastRAF = t;

    let delta = elapsed / TARGET_DELTA;
    currentFPS = 1000 / elapsed;

    if(isNaN(delta)) {
        delta = 1;
    }

    for(const id in engineInstances) {
        const engine = engineInstances[id];
        engine.render();
        engine.update(t, delta);
    }
}

function renderScrollInstance(engine, delta) {
    if(!engine.running) {
        return;
    }

    if(engine.autoScale) {
        engine.scale = window.devicePixelRatio || 1;
    }

    if(engine.scale != engine.lastScale) {
        resizeInstance(engine);
    }

    engine.lastScale = engine.scale;

    engine.renderOrder = 0;
    engine.lightBlockers = [];

    if(engine.particleEngine) {
        engine.particleEngine.update(delta);
    }

    for(const popper of engine.textPoppers) {
        if(!popper.cashed) {
            popper.y -= 2 * delta;
            popper.alpha -= 0.03 * delta;
        }
    }

    let fullCanvas = null;
    let fullContext = null;

    if(engine.fullMapRenderCallback) {
        const umapTotalWidth = engine.mapWidth * engine.gridSize;
        const umapTotalHeight = engine.mapHeight * engine.gridSize;

        fullCanvas = document.createElement("canvas");
        fullContext = fullCanvas.getContext("2d");

        if(engine.pixelated) {
            pixelateCanvas(fullCanvas);
        }

        fullCanvas.width = umapTotalWidth / 2;
        fullCanvas.height = umapTotalHeight / 2;

        if(engine.isometricMode) {
            fullCanvas.height = umapTotalHeight / 4;
        }
    }

    engine.fpsCounter++;

    if(engine.fpsCounter < engine.fpsLimiter) {
        return;
    }

    engine.fpsCounter = 0;

    engine.instructionsRecieved = false;

    if(engine.drawFunction) {
        let fullRender = false;

        if(fullContext) {
            fullRender = true;
        }

        engine.drawFunction(fullRender);
    }

    if(!engine.instructionsRecieved) {
        return;
    }

    if(engine.changed) {
        engine.staticContext.clearRect(0, 0, engine.width, engine.height);
        engine.staticContext.save();
        engine.staticContext.translate(-engine.viewX, -engine.viewY);

        doStaticRender(engine, fullContext);

        engine.staticContext.restore();

        engine.changed = false;
    }

    engine.context.clearRect(0, 0, engine.width, engine.height);
    engine.context.globalCompositeOperation = "source-over";

    if(engine.staticCanvas && engine.staticCanvas.width > 0) {
        engine.context.save();
        engine.context.setTransform(1, 0, 0, 1, 0, 0); 
        engine.context.drawImage(engine.staticCanvas, 0, 0, engine.width, engine.height);
        engine.context.restore();
    }

    if(engine.drawQueue.length > 0) {
        engine.drawQueue.sort(sortRenderItemReverse);

        while(engine.drawQueue.length > 0) {
            const item = engine.drawQueue.pop();
            performRenderOnItem(engine, item, engine.context, fullContext);
            usedRenderObjects.push(item);
        }
    }

    engine.context.globalAlpha = 1;

    if(engine.lightSources.length > 0 || engine.colorFilter != null) {
        if(engine.colorFilter != null && engine.filterAmount > 0) {
            const darkRGB = hexToRGB(engine.colorFilter);

            engine.darknessMaskColor = 
            "rgba(" + 
                darkRGB.r + 
                "," + 
                darkRGB.g + 
                "," + 
                darkRGB.b + 
                "," + 
                engine.filterAmount + 
            ")";
        } else {
            engine.darknessMaskColor = null;
        }

        let useOff = "rgba(255,255,255,0)";
        
        if(engine.darknessMaskColor != null) {
            useOff = engine.darknessMaskColor;
        }

        engine.lightContext.fillStyle = useOff;
        engine.lightContext.clearRect(0, 0, engine.width, engine.height);
        engine.lightContext.fillRect(0, 0, engine.width, engine.height);

        engine.lightFinalRenderContext.clearRect(0, 0, engine.width, engine.height);

        while(engine.lightSources.length > 0) {
            const source = engine.lightSources.pop();

            const useX = (0.5 + (source.x - engine.viewX)) | 0;
            const useY = (0.5 + (source.y - engine.viewY)) | 0;

            const radius = source.radius;

            ligthenGradient(
                engine,
                engine.lightContext, 
                useX, 
                useY, 
                radius, 
                "rgba(" + 
                    source.color.r + "," + 
                    source.color.g + "," + 
                    source.color.b + "," + 
                    source.intensity + 
                ")", 
                "rgba(" + 
                    source.color.r + "," + 
                    source.color.g + "," + 
                    source.color.b + ",0)"
            );

            lightInstructionRecycling.push(source);
        }

        if(engine.canvas && engine.width > 0 && engine.height > 0) {
            engine.lightFinalRenderContext.globalCompositeOperation = "source-over";
            engine.lightFinalRenderContext.drawImage(engine.canvas, 0, 0);
        }

        if(engine.lightCanvas && engine.width > 0 && engine.height > 0) {
            engine.lightFinalRenderContext.globalCompositeOperation = "source-in";
            engine.lightFinalRenderContext.drawImage(engine.lightCanvas, 0, 0);
        }

        engine.context.save();
        engine.context.globalCompositeOperation = "multiply";
        engine.context.drawImage(engine.lightFinalRenderCanvas, 0, 0);
        engine.context.restore();
    }
    
    if(engine.aboveFoldDrawQueue.length > 0) {
        engine.aboveFoldDrawQueue.sort(sortRenderItemReverse);

        while(engine.aboveFoldDrawQueue.length > 0) {
            const item = engine.aboveFoldDrawQueue.pop();
            performRenderOnItem(engine, item, engine.context, fullContext);
            usedRenderObjects.push(item);
        }
    }

    if(engine.particleEngine) {
        engine.particleEngine.draw(engine.context);
    }

    if(engine.screenshotPhase) {
        engine.screenshotPhase = false;
        engine.changed = true;

        engine.screenshotContext.drawImage(engine.canvas, 0, 0);

        if(engine.screenshotCallback) {
            engine.screenshotCallback(engine.screenshotCanvas);
        }

        engine.screenshotCanvas = null;
        engine.screenshotContext = null;
        engine.screenshotCallback = null;
    }

    const popperKillArray = [];

    for(const popper of engine.textPoppers) {
        if(popper.cashed) {
            popperKillArray.push(popper);
        } else {
            renderTextPopper(engine, engine.context, popper);
        }
    }

    while(popperKillArray.length > 0) {
        const popper = popperKillArray.pop();
        removeFromArray(engine.textPoppers, popper);
        usedPopperObjects.push(popper);
    }

    if(engine.isSelection && !engine.isPinching) {
        engine.context.save();
        engine.context.globalAlpha = 1;
        engine.context.lineWidth = 4;
        engine.context.strokeStyle = engine.selectionColor;

        engine.context.strokeRect(engine.selectionTopX, engine.selectionTopY, engine.selectionWidth, engine.selectionHeight);

        engine.context.restore();
    }

    if(engine.fullMapRenderCallback && fullCanvas) {

        const cb = engine.fullMapRenderCallback;

        const fullMap = new Image();
        fullMap.onload = function() {
            cb(fullMap);
        };
        fullMap.src = fullCanvas.toDataURL("image/png");
    }

    engine.fullMapRenderCallback = null;

    if(engine.lerpCallback) {
        const position = engine.getCenterPosition();
        const dist = distBetweenPoints(position.px, position.py, engine.lerpX, engine.lerpY);

        if(dist < engine.lerpAccuracy) {
            const LCB = engine.lerpCallback;
            
            engine.lerpX = 0;
            engine.lerpY = 0;

            engine.lerpCallback = null;
            engine.lerpSpeed = 0.15;
            engine.lerpAccuracy = 1;

            LCB();
        } else {
            let lx = (engine.lerpX - position.px) * engine.lerpSpeed;
            let ly = (engine.lerpY - position.py) * engine.lerpSpeed;
    
            if(lx > 0 && lx < MIN_LERP) {
                lx = MIN_LERP;
            }
    
            if(lx < 0 && lx > -MIN_LERP) {
                lx = -MIN_LERP;
            }
    
            if(ly > 0 && ly < MIN_LERP) {
                ly = MIN_LERP;
            }
    
            if(ly < 0 && ly > -MIN_LERP) {
                ly = -MIN_LERP;
            }
    
            const nx = position.px + lx;
            const ny = position.py + ly;

            engine.centerOnCoord(nx, ny);
        }

        

        
    }
}

function absoluteAndFillElement(element) {
    element.style.position = "absolute";
    element.style.left = "0";
    element.style.top = "0";
    element.style.width = "100%";
    element.style.height = "100%";
    element.style.overflow = "hidden";
}

function onInstanceDown(engine, e) {

    let x = e.x;
    let y = e.y;

    let ox = x;
    let oy = y;

    engine.didAMove = false;
    

    if(e.type == "touch") {
        engine.usingTouch = true;
    } else {
        engine.usingTouch = false;
    }

    const pointer = engine.getPointer(e.id, ox, oy, e.type);
    pointer.down = true;

    engine.pointersDown++;

    engine.isSelection = false;

    if(engine.nextDownSelection) {
        engine.isSelection = true;
        engine.nextDownSelection = false;
    }

    engine.actualX = ox;
    engine.actualY = oy;

    if(e.type == "mouse") {
        engine.usingMouse = true;

        if(e.which && e.which != 1) {
            pointer.rightClick = true;
        } else {
            pointer.rightClick = false;
        }
    } else {
        engine.usingMouse = false;
    }

    if(engine.pointerListener) {
        engine.pointerListener("down", x, y, e.type, e.which);
    }

    engine.startX = x;
    engine.startY = y;
    engine.didMove = false;
    engine.isDown = true;
    engine.isHold = false;

    if(engine.holdFunction || engine.selectionFunction) {
        engine.holdX = x;
        engine.holdY = y;

        if(!pointer.rightClick && !engine.isSelection) {
            engine.holdTimer = setTimeout(function() {
                engine.holdTimer = null;
                engine.didMove = false;

                if(engine.isPainting) {
                    return;
                }

                if(engine.selectionFunction) {
                    beginSelection(engine);
                    return;
                }

                if(engine.holdFunction) {
                    engine.isHold = true;
                    const position = engine.positionToCoords(engine.holdX, engine.holdY);
                    engine.holdFunction(position.x, position.y);
                }
            }, 700);
        } else {
            if(engine.selectionFunction && engine.isSelection) {
                beginSelection(engine);
            }
        }
    }

    if(engine.pointersDown > 1) {
        engine.isSelection = false;

        if(engine.holdTimer) {
            clearTimeout(engine.holdTimer);
            engine.holdTimer = null;
        }
    }
}

function onInstanceMove(engine, e) {
    if(e.type == "touch") {
        engine.usingTouch = true;
    } else {
        engine.usingTouch = false;
    }

    const pointer = engine.getPointer(e.id, e.x, e.y, e.type);
    pointer.down = true;

    engine.actualX = e.x;
    engine.actualY = e.y;

    if(e.type == "mouse") {
        engine.usingMouse = true;
    } else {
        engine.usingMouse = false;
    }

    let x = e.x;
    let y = e.y;

    if(engine.pointerListener) {
        engine.pointerListener("move", x, y, e.type, e.which);
    }

    pointer.x = x;
    pointer.y = y;

    if(engine.pointersDown == 2) {
        engine.didMove = true;
        handlePinch(engine);
        return;
    }

    let oldX = 0;
    let oldY = 0;

    if(engine.curX) {
        oldX = engine.curX;
        oldY = engine.curY;
    }

    engine.curX = x;
    engine.curY = y;

    const position = engine.positionToCoords(x, y);

    if((e.type == "mouse" || e.type == "pen") && engine.hoverFunction) {
        engine.lastHoverX = position.x;
        engine.lastHoverY = position.y;

        engine.hoverFunction(position.x, position.y, engine.actualX, engine.actualY, e.type, position.px, position.py);
    }

    if(!engine.isDown || engine.isHold) {
        return;
    }

    if(engine.isSelection) {
        engine.setSelectionPoints(x, y);

        if(engine.selectionProgressFunction) {
            engine.sendSelectionPointsToFunction(engine.selectionProgressFunction);
        }

        return;
    }

    if(engine.didMove) {
        engine.changed = true;

        if(engine.isPainting && engine.paintFunction) {
            if(engine.lastPaintX == position.x && engine.lastPaintY == position.y) {
                return;
            }

            engine.lastPaintX = position.x;
            engine.lastPaintY = position.y;

            engine.paintFunction(position.x, position.y, engine.actualX, engine.actualY, e.type);
            return;
        }

        engine.didAMove = true;

        const difX = oldX - engine.curX;
        const difY = oldY - engine.curY;

        engine.viewX += difX;
        engine.viewY += difY;

        engine.checkBounds();
        engine.notifyViewportChange(true);

    } else {
        const dist = distBetweenPoints(engine.startX, engine.startY, x, y);

        let moveMax = 6;

        if(engine.usingTouch) {
            moveMax = 12;
        }

        if(dist > moveMax) {
            engine.didMove = true;

            if(engine.holdTimer) {
                clearTimeout(engine.holdTimer);
                engine.holdTimer = null;
                engine.isHold = false;
            }
        }
    }
}

function onInstanceUp(engine, e) {
    if(engine.didAMove) {
        engine.didAMove = false;
    }

    if(e.type == "touch") {
        engine.usingTouch = true;
    } else {
        engine.usingTouch = false;
    }

    const pointer = engine.getPointer(e.id, null, null, e.type);

    if(pointer.down) {
        engine.pointersDown--;
        pointer.down = false;
    }

    if(engine.holdTimer) {
        clearTimeout(engine.holdTimer);
        engine.holdTimer = null;
        engine.isHold = false;
    }

    if(pointer.primary) {
        pointer.primary = false;
        engine.primaryPointer = null;
    }

    if(engine.isPinching) {
        engine.isSelection = false;
    }

    engine.isPinching = false;

    if(!engine.isDown) {
        return;
    }

    if(engine.isHold) {
        engine.isDown = false;

        if(engine.releaseFunction) {
            engine.releaseFunction();
        }

        return;
    }

    engine.isPainting = false;

    if(engine.pointersDown <= 0) {
        engine.pointers = {};
        engine.pointersDown = 0;
        engine.primaryPointer = null;
        engine.lastDistance = null;
    }

    if(engine.isSelection) {
        processSelection(engine);
        return;
    }

    if(!engine.didMove && engine.clickFunction) {
        const position = engine.positionToCoords(engine.startX, engine.startY);

        engine.isSelection = false;
        engine.isDown = false;

        engine.pointersDown = 0;

        const ax = engine.actualX;
        const ay = engine.actualY;

        if(e.type == "touch") {
            setTimeout(function() {
                engine.clickFunction(position.x, position.y, ax, ay, e.type, position.px, position.py);
            }, 75);
        } else {
            if(pointer.rightClick && engine.rightClickFunction) {
                engine.rightClickFunction(position.x, position.y, ax, ay, e.type, position.px, position.py);
            } else {
                engine.clickFunction(position.x, position.y, ax, ay, e.type, position.px, position.py);
            }

            pointer.rightClick = false;
        }
    }

    if(engine.pointerListener) {
        engine.pointerListener("up", 0, 0, e.type, e.which);
    }

    engine.isDown = false;
    engine.didMove = false;

    engine.actualX = 0;
    engine.actualY = 0;
}

function onInstanceWheel(engine, e) {
    if(!engine.usingMouse) {
        return;
    }

    const normalized = normalizeWheel(e);

    if(e.deltaY < 0) {
        engine.doZoom(true, normalized.spinY);
    }

    if(e.deltaY > 0) {
        engine.doZoom(false, normalized.spinY);
    }
}

function beginSelection(engine) {
    engine.isSelection = true;

    engine.selectionX = engine.holdX;
    engine.selectionY = engine.holdY;

    engine.setSelectionPoints(engine.holdX, engine.holdY);

    if(engine.selectionProgressFunction) {
        engine.sendSelectionPointsToFunction(engine.selectionProgressFunction);
    }
}

function handlePinch(engine) {
    if(engine.pointersDown != 2 || !engine.primaryPointer) {
        return;
    }

    let pointer1, pointer2;

    for(const id in engine.pointers) {
        const pointer = engine.pointers[id];

        if(!pointer.down) {
            continue;
        }

        if(!pointer1) {
            pointer1 = pointer;
        } else {
            if(!pointer2) {
                pointer2 = pointer;
            }
        }
    }

    if(!pointer1 || !pointer2) {
        return;
    }

    engine.isSelection = false;

    const dist = distBetweenPoints(pointer1.x, pointer1.y, pointer2.x, pointer2.y);

    if(engine.lastDistance == null) {
        engine.lastDistance = dist;
        return;
    }

    if(dist > engine.lastDistance + 3) {
        engine.doZoom(true);
        engine.lastDistance = dist;
    }

    if(dist < engine.lastDistance - 3) {
        engine.doZoom(false);
        engine.lastDistance = dist;
    }
}

function processSelection(engine) {
    engine.isSelection = false;
    engine.isDown = false;

    if(engine.selectionFunction) {
        engine.sendSelectionPointsToFunction(engine.selectionFunction);
    }
}

function normalizeWheel(/*object*/ event) /*object*/ {
    let sX = 0, sY = 0,       // spinX, spinY
        pX = 0, pY = 0;       // pixelX, pixelY

    // Legacy
    if ("detail"      in event) { sY = event.detail; }
    if ("wheelDelta"  in event) { sY = -event.wheelDelta / 120; }
    if ("wheelDeltaY" in event) { sY = -event.wheelDeltaY / 120; }
    if ("wheelDeltaX" in event) { sX = -event.wheelDeltaX / 120; }

    // side scrolling on FF with DOMMouseScroll
    if ( "axis" in event && event.axis === event.HORIZONTAL_AXIS ) {
        sX = sY;
        sY = 0;
    }

    pX = sX * PIXEL_STEP;
    pY = sY * PIXEL_STEP;

    if ("deltaY" in event) { pY = event.deltaY; }
    if ("deltaX" in event) { pX = event.deltaX; }

    if ((pX || pY) && event.deltaMode) {
        if (event.deltaMode == 1) {          // delta in LINE units
            pX *= LINE_HEIGHT;
            pY *= LINE_HEIGHT;
        } else {                             // delta in PAGE units
            pX *= PAGE_HEIGHT;
            pY *= PAGE_HEIGHT;
        }
    }

    // Fall-back if spin cannot be determined
    if (pX && !sX) { sX = (pX < 1) ? -1 : 1; }
    if (pY && !sY) { sY = (pY < 1) ? -1 : 1; }

    return { 
        pinX  : sX,
        spinY  : sY,
        pixelX : pX,
        pixelY : pY 
    };
}

function doStaticRender(engine, fullContext) {
    if(!engine.staticCallMade) {
        return;
    }

    if(!engine.viewBounds) {
        engine.setViewBounds();
    }

    let minX = engine.viewBounds.minX;
    let minY = engine.viewBounds.minY;
    let maxX = engine.viewBounds.maxX;
    let maxY = engine.viewBounds.maxY;

    if(fullContext) {
        minX = 0;
        minY = 0;
        maxX = engine.mapWidth;
        maxY = engine.mapHeight;
    }

    for(let z = 0; z <= engine.staticMaxZIndex; z++) {
        for(let x = minX; x <= maxX; x++) {
            for(let y = minY; y <= maxY; y++) {
                const renderItem = engine.getStaticItem(x, y, z);

                if(!renderItem || !renderItem.img) {
                    continue;
                }

                engine.staticContext.drawImage(renderItem.img, renderItem.x, renderItem.y, renderItem.w, renderItem.h);
            }
        }
    }
}

function sortRenderItemReverse(b,a) {
    if(a.zIndex > b.zIndex) {
        return 1;
    }

    if(a.zIndex < b.zIndex) {
        return -1;
    }

    if(a.nearness > b.nearness) {
        return 1;
    }

    if(a.nearness < b.nearness) {
        return -1;
    }

    if(a.cX > b.cX) {
        return 1;
    }

    if(a.cX < b.cX) {
        return -1;
    }
    

    if(a.cY > b.cY) {
        return 1;
    }

    if(a.cY < b.cY) {
        return -1;
    }

    if(a.ro > b.ro) {
        return 1;
    }

    if(a.ro < b.ro) {
        return -1;
    }

    return 0;
}

function performRenderOnItem(engine, item, context, fullContext) {
    let useX, useY;

    if(engine.isometricMode) {
        const offsetX = (item.tileWidth - 1) * engine.halfRelativeGridSize;
        const offsetY = (item.tileHeight - 1) * engine.quarterRelativeGridSize;

        useX = item.x - engine.viewX - offsetX;
        useY = item.y - engine.viewY - offsetY;


        /*
        useX = item.x - engine.viewX - ((item.tileWidth - 1) * engine.halfRelativeGridSize);
        useY = item.y - engine.viewY - ((item.tileHeight - 1) * engine.quarterRelativeGridSize);
        */

        /*
        useX = item.x - engine.viewX;
        useY = item.y - engine.viewY;
        */
    } else {
        useX = (0.5 + (item.x - engine.viewX)) | 0;
        useY = (0.5 + (item.y - engine.viewY)) | 0;
    }

    if(fullContext && !item.isLine && !item.isCircle) {
        if((useX + item.w) < 0 || (useY + item.h) < 0 || useX > engine.width || useY > engine.height) {
            if(!item.isBar && !item.isLine && !item.isSquare) {
                addToFullMap(engine, fullContext, item.img, item.tX, item.tY);
            }

            return;
        }
    }

    if(item.isLine && (useX > engine.winWidth || useY > engine.winHeight)) {
        return;
    }

    if(item.blocksLight && !engine.isometricMode) {
        let lbY = useY;

        if(engine.doubleHeightTiles) {
            lbY += engine.relativeGridSize;
        }

        engine.lightBlockers.push({
            x: useX,
            y: lbY
        });
    }

    if(item.isText) {
        performTextRender(engine, context, item, useX, useY);
        return;
    }

    if(item.isLine) {
        performLineRender(engine, context, item, useX, useY);
        return;
    }

    if(item.isCircle) {
        performCircleRender(engine, context, item, useX, useY);
        return;
    }

    if(item.isSquare) {
        performSquareRender(engine, context, item, useX, useY);
        return;
    }

    if(item.isBar) {
        performBarRender(engine, context, item, useX, useY);
        return;
    }

    if(item.alpha != undefined && item.alpha != null) {
        context.globalAlpha = item.alpha;
    } else {
        context.globalAlpha = 1;
    }

    if(item.segmentX > 0) {
        performSegmentedRender(engine, context, item, useX, useY);
        return;
    }

    performStandardRender(engine, context, item, useX, useY, fullContext);
}

function renderTextPopper(engine, context, popper) {
    if(popper.alpha <= 0) {
        popper.cashed = true;
        return;
    }

    const useX = popper.x - engine.viewX;
    const useY = popper.y - engine.viewY;

    const fontSize = 20 * engine.zoomLevel;

    context.setLineDash([]);
    context.strokeStyle = "#000000";
    context.lineWidth = 1;

    context.fillStyle = popper.color;
    context.textAlign = "center";
    context.textBaseline = "middle";
    context.font = "bold " + fontSize + "px sans-serif";
    
    context.save();
    context.globalAlpha = popper.alpha;
    
    context.fillText(popper.text,useX,useY);
    context.strokeText(popper.text,useX,useY);
    
    context.restore();
}

function addToFullMap(engine, fullContext, img, x, y) {
    if(!fullContext) {
        return;
    }

    let dx = Math.floor(x * engine.gridSize) / 2;
    let dy = (((y - 1) * engine.gridSize) / 2) - (img.height / 2);

    if(engine.isometricMode) {
        dx = Math.floor((x - y) * engine.halfRelativeGridSize) / 2;
        dy = (((x + y) * engine.quarterRelativeGridSize) / 2);

        dx += fullContext.canvas.width / 2;
    }

    fullContext.drawImage(img, dx, dy, (img.width / 2), (img.height / 2));
}

function performTextRender(engine, context, item, useX, useY) {

    const fontSize = (item.lineWidth * engine.zoomLevel);

    context.setLineDash([]);
    context.textBaseline = "middle";

    let fnt = context.font = "bold " + fontSize + "px sans-serif";

    if(item.textFont) {
        fnt = "bold " + fontSize + "px " + item.textFont;
    }

    drawStroked(context, fnt, item.color, item.barColor, item.isText, useX, useY, 2, engine.zoomLevel);
}

function drawStroked(ctx, font, fill, stroke, text, x, y, width, zoomLevel) {
    if(!stroke) {
        stroke = "#000000";
    }

    if(!font) {
        let fntSize = Math.round(12 * zoomLevel);
        font = "bold " + fntSize + "px sans-serif";
    }

    if(!fill) {
        fill = "#ffffff";
    }

    if(!width) {
        width = 1;
    }

    ctx.textAlign = "center";
    ctx.font = font;
    ctx.strokeStyle = stroke;
    ctx.lineWidth = width;

    ctx.lineJoin = "miter"; 

    ctx.miterLimit = 2;
    ctx.strokeText(text, x, y);
    ctx.fillStyle = fill;
    ctx.fillText(text, x, y);
}

function performLineRender(engine, context, item, useX, useY) {
    const useX2 = (0.5 + (item.w - engine.viewX)) | 0;
    const useY2 = (0.5 + (item.h - engine.viewY)) | 0;

    context.lineWidth = item.lineWidth;
    context.strokeStyle = item.color;
    context.globalAlpha = item.alpha;

    if(item.dashedLine) {
        context.setLineDash([4, 10]);
    } else {
        context.setLineDash([]);
    }

    context.beginPath();

    context.moveTo(useX, useY);
    context.lineTo(useX2, useY2);

    context.stroke();
}

function performCircleRender(engine, context, item, useX, useY) {
    if(item.lineWidth > 0) {
        context.lineWidth = item.lineWidth;
        context.strokeStyle = item.color;

        if(item.dashedLine) {
            context.setLineDash([4,10]);
        } else {
            context.setLineDash([]);
        }
    } else {
        context.fillStyle = item.color;
    }

    context.globalAlpha = item.alpha;

    context.beginPath();
    
    if(engine.isometricMode) {
        context.ellipse(
            useX,
            useY,
            item.h,
            (item.h / 2),
            0, 
            0, 
            TWO_π
        );
    } else {
        context.ellipse(useX, useY, item.h, item.h, 0, 0, TWO_π);
    }
    
    if(item.lineWidth > 0) {
        context.stroke();
    } else {
        context.fill();
    }
}

function performSquareRender(engine, context, item, useX, useY) {
    context.fillStyle = item.color;
    context.globalAlpha = 1;

    if(item.img) {
        context.save();
        context.globalCompositeOperation = item.img;
    }
    
    if(engine.isometricMode) {
        context.beginPath();
        context.moveTo(useX,useY);

        context.lineTo(useX + engine.halfRelativeGridSize, (useY + engine.quarterRelativeGridSize));
        context.lineTo(useX,(useY + engine.halfRelativeGridSize));
        context.lineTo(useX - engine.halfRelativeGridSize, (useY + engine.quarterRelativeGridSize));
        
        context.fill();
    } else {
        context.fillRect(
            useX,
            useY,
            (engine.relativeGridSize + 1),
            (engine.relativeGridSize + 1)
        );
    }

    if(item.img) {
        context.restore();
    }
}

function performBarRender(engine, context, item, useX, useY) {
    const barWidth = item.barWidth;
    let meterWidth = item.meterWidth;
    
    if(meterWidth < 0) {
        meterWidth = 0;
    }
    
    context.globalAlpha = 1;
    
    context.fillStyle = "#000000";
    context.fillRect(useX, useY, barWidth, 6);
    
    context.fillStyle = item.barColor;
    context.fillRect((useX + 1), (useY + 1), meterWidth, 4);
}

function performSegmentedRender(engine, context, item, useX, useY) {
    if((useY + item.h) < 0) {
        return;
    }

    if(((useX + item.destSegX) + engine.halfRelativeGridSize) < 0) {
        return;
    }

    context.drawImage(
        item.img,
        item.segmentX,
        0,
        item.sW,
        item.sH,
        (useX + item.destSegX),
        useY,
        (engine.halfRelativeGridSize + SEGMENTED_RENDER_BUFFER),
        item.h
    );
}

function performStandardRender(engine, context, item, useX, useY, fullContext) {
    if(item.angle != 0) {
        context.save();
        
        context.translate(
            useX + engine.halfRelativeGridSize,
            useY + engine.halfRelativeGridSize
        );

        context.rotate(item.angle * ONE_EIGHTY_π);

        useX = -engine.halfRelativeGridSize;
        useY = -engine.halfRelativeGridSize;
    }

    if(item.img) {
        context.drawImage(item.img, useX, useY, item.w, item.h);
    }

    if(item.angle != 0) {
        context.restore();
    }

    if(fullContext) {
        addToFullMap(engine, fullContext, item.img, item.tX, item.tY);
    }
}

function ligthenGradient(engine, context, x, y, radius, from, off) {

    if(!radius || isNaN(radius) || radius < 0) {
        return;
    }

    let radialGradient;

    if(engine.isometricMode) {
        if(radius > (engine.relativeGridSize * 0.8)) {
            context.save();

            context.transform(1, 0, 0, 0.5, 0, 0);

            radialGradient = context.createRadialGradient(
                x, 
                (y * 2), 
                0, 
                x, 
                (y * 2), 
                radius
            );

            radialGradient.addColorStop(0.0, from);
            radialGradient.addColorStop(1,off);
    
            context.fillStyle = radialGradient;
            context.beginPath();
            
            context.arc(x, (y * 2), radius, 0, TWO_π);

            context.fill();
            context.restore();

        } else {

            radialGradient = context.createRadialGradient(
                x, 
                y,
                0, 
                x,
                y,
                radius
            );

            radialGradient.addColorStop(0.0, from);
            radialGradient.addColorStop(1, off);
    
            context.fillStyle = radialGradient;
            context.beginPath();

            context.arc(x, y, radius, 0, TWO_π);
            context.fill();
        }
        
        return;
    }

    engine.preRenderCanvas.height = radius * 2;
    engine.preRenderCanvas.width = radius * 2;

    engine.gradientFilterCanvas.height = radius * 2;
    engine.gradientFilterCanvas.width = radius * 2;

    let blockingItems = [];
    let i,a,b,c,j,blocker;

    
    if(!engine.isometricMode) {
        for(i = 0; i < engine.lightBlockers.length; i++) {

            blocker = engine.lightBlockers[i];

            a = x - blocker.x;
            b = y - blocker.y;
            
            c = Math.sqrt( a*a + b*b );

            if(c <= radius + (radius * 0.05)) {
                blocker.d = c;
                blockingItems.push(blocker);
            }
        }
    }

    blocker = null;


    if(engine.isometricMode && radius > (engine.relativeGridSize * 0.8)) {
        engine.preRenderContext.save();

        engine.preRenderContext.transform(1,0,0,0.5,0,0);

        radialGradient = context.createRadialGradient(
            radius, 
            radius * 2, 
            0, 
            radius, 
            radius * 2, 
            radius
        );
        
        radialGradient.addColorStop(0.0, from);
        radialGradient.addColorStop(1,off);

        engine.preRenderContext.fillStyle = radialGradient;
        engine.preRenderContext.beginPath();
        
        engine.preRenderContext.arc(radius, radius * 2, radius, 0, TWO_π);

        engine.preRenderContext.fill();
        engine.preRenderContext.restore();

    } else {

        radialGradient = context.createRadialGradient(
            radius, 
            radius, 
            0, 
            radius, 
            radius, 
            radius
        );
              
        radialGradient.addColorStop(0.0, from);
        radialGradient.addColorStop(1,off);

        engine.preRenderContext.fillStyle = radialGradient;
        engine.preRenderContext.beginPath();

        engine.preRenderContext.arc(radius, radius, radius, 0, TWO_π);
        engine.preRenderContext.fill();
    }
    
    if(engine.isometricMode) {
        context.save();
        context.globalCompositeOperation = "lighten";
        context.drawImage(engine.preRenderCanvas, x - radius, y - radius);

        context.restore();
        return;
    }

    let allRays = [];
    let allSides = [];


    for(i = 0; i < 360; i++) {
        const ox0 = radius + (radius + radius * 0.05) * Math.cos(i);
        const oy0 = radius + (radius + radius * 0.05) * Math.sin(i);

        allRays.push({
            x: ox0, y:oy0
        });
    }
    

    while(blockingItems.length > 0) {
        processBlockingItem(engine, blockingItems.pop(),radius,allSides,x,y);
    }
    
    let sourceBlocks = [];
    
    for(i = 0, j = allRays.length; i < j; i++) {
        processRay(allRays[i],radius,allSides,sourceBlocks);
    }

    engine.gradientFilterContext.fillStyle = "rgba(0,0,0,.3)";
    engine.gradientFilterContext.fillRect(
        0,
        0,
        engine.gradientFilterCanvas.width,
        engine.gradientFilterCanvas.height
    );

    engine.gradientFilterContext.fillStyle = "#ff0000";

    for(i = 0, j = sourceBlocks.length; i < j; i++) {
        engine.gradientFilterContext.fillRect(
            sourceBlocks[i].x,
            sourceBlocks[i].y,
            engine.relativeGridSize,
            engine.relativeGridSize
        );
    }

    allRays.sort(sortRayAngle);

    engine.gradientFilterContext.beginPath();
    engine.gradientFilterContext.moveTo(allRays[0].x,allRays[0].y);
    for(i = 1, j = allRays.length; i < j; i++) {
        engine.gradientFilterContext.lineTo(allRays[i].x,allRays[i].y);
    }

    engine.gradientFilterContext.closePath();
    engine.gradientFilterContext.fill();

    engine.preRenderContext.save();
    
    engine.preRenderContext.globalCompositeOperation = "destination-in";
    engine.preRenderContext.drawImage(engine.gradientFilterCanvas, 0, 0);
    engine.preRenderContext.restore();

    context.save();
    context.globalCompositeOperation = "lighten";
    context.drawImage(engine.preRenderCanvas, x - radius, y - radius);

    context.restore();
}

function sortRayAngle(a,b) {
    if(a.angle > b.angle) {
        return 1;
    }

    if(a.angle < b.angle) {
        return -1;
    }
}

function processBlockingItem(engine, item, radius, allSides, x, y) {
    const angleZ = Math.atan2(item.y - y, item.x - x);

    const baseX = radius + item.d * Math.cos(angleZ);
    const baseY = radius + item.d * Math.sin(angleZ);


    const topLeft = {x: baseX, y: baseY };
    const topRight = {x: baseX + engine.relativeGridSize, y: baseY };
    const bottomLeft = {x: baseX, y: baseY + engine.relativeGridSize };

    const bottomRight = {
        x: baseX + engine.relativeGridSize, 
        y: baseY + engine.relativeGridSize 
    };

    allSides.push({
        x1: topLeft.x,
        y1: topLeft.y,
        x2: topRight.x,
        y2: topRight.y,
        source: topLeft
    });

    allSides.push({
        x1: topRight.x,
        y1: topRight.y,
        x2: bottomRight.x,
        y2: bottomRight.y,
        source: topLeft
    });

    allSides.push({
        x1: bottomLeft.x,
        y1: bottomLeft.y,
        x2: bottomRight.x,
        y2: bottomRight.y,
        source: topLeft
    });

    allSides.push({
        x1: topLeft.x,
        y1: topLeft.y,
        x2: bottomLeft.x,
        y2: bottomLeft.y,
        source: topLeft
    });
}

function processRay(ray,radius,allSides,sourceBlocks) {
    let closestHit = 99999999;
    let closestSource = null;

    let a,b,c;
    
    for(let k = 0, l = allSides.length; k < l; k++) {

        const side = allSides[k];

        const topIntersect = checkLineIntersection(
            radius,
            radius,
            ray.x,
            ray.y,
            side.x1,
            side.y1,
            side.x2,
            side.y2
        );

        if(topIntersect.onLine1 && topIntersect.onLine2) {
            
            a = radius - topIntersect.x;
            b = radius - topIntersect.y;
            
            c = Math.sqrt( a*a + b*b );

            if(c < closestHit) {
                ray.x = topIntersect.x;
                ray.y = topIntersect.y;
                closestHit = c;

                if(side.source) {
                    closestSource = side.source;
                }
            }

        }
    }

    if(closestSource != null) {
        sourceBlocks.push(closestSource);
    }

    ray.angle = Math.atan2(ray.y - radius, ray.x - radius);
}

function checkLineIntersection(
    line1StartX, 
    line1StartY, 
    line1EndX, 
    line1EndY, 
    line2StartX, 
    line2StartY, 
    line2EndX, 
    line2EndY
) {
    let denominator, a, b, numerator1, numerator2, result = {
        x: null,
        y: null,
        onLine1: false,
        onLine2: false
    };

    denominator = 
        ((line2EndY - line2StartY) * (line1EndX - line1StartX)) - 
        ((line2EndX - line2StartX) * (line1EndY - line1StartY));

    if (denominator == 0) {
        return result;
    }

    a = line1StartY - line2StartY;
    b = line1StartX - line2StartX;

    numerator1 = 
        ((line2EndX - line2StartX) * a) - ((line2EndY - line2StartY) * b);

    numerator2 = 
        ((line1EndX - line1StartX) * a) - ((line1EndY - line1StartY) * b);

    a = numerator1 / denominator;
    b = numerator2 / denominator;

    result.x = line1StartX + (a * (line1EndX - line1StartX));
    result.y = line1StartY + (a * (line1EndY - line1StartY));

    if (a > 0 && a < 1) {
        result.onLine1 = true;
    }

    if (b > 0 && b < 1) {
        result.onLine2 = true;
    }

    return result;
}

function doDrawStaticTile(engine, img, x, y, zIndex) {
    if(img == undefined) {
        return;
    }

    if(x < 0 || x > engine.mapWidth) {
        return;
    }

    if(y < 0 || y > engine.mapHeight) {
        return;
    }

    if(!zIndex) {
        zIndex = 0;
    }

    if(zIndex > engine.staticMaxZIndex) {
        engine.staticMaxZIndex = zIndex;
        engine.initStaticMap();

        engine.changed = true;
    }

    if(engine.fullMapRenderCallback) {
        doDrawTile(engine, img, x, y, zIndex, false, 1);
        return;
    }

    engine.staticCallMade = true;

    if(!engine.staticMapInit) {
        engine.initStaticMap();
    }

    engine.instructionsRecieved = true;

    const existingItem = engine.getStaticItem(x, y, zIndex);

    if(existingItem == null) {
        engine.setStaticItem(x, y, zIndex, buildRenderObjectForTile(engine, img, x, y));
        engine.changed = true;
    } else {
        if(existingItem.img != img) {
            engine.setStaticItem(
                x,
                y,
                zIndex, 
                buildRenderObjectForTile(engine, img, x, y, existingItem)
            );

            engine.changed = true;
        }
    }
}

function doDrawTile(engine, img, x, y, zIndex = 0, blocksLight = false, alpha = 1) {
    if(!engine.drawQueue || img == undefined || img == null) {
        return;
    }

    engine.instructionsRecieved = true;

    if(!engine.checkVisibility(x, y) && !engine.fullMapRenderCallback) {
        return;
    }

    const item = buildRenderObjectForTile(engine, img, x, y, null);

    item.tX = x;
    item.tY = y;

    item.nearness = y;
    item.alpha = alpha;
    item.blocksLight = blocksLight;
    item.zIndex = zIndex;

    if(engine.isometricMode) {
        item.nearness += x;
    }

    engine.drawQueue.push(item);
}

function buildRenderObjectForTile(engine, img, x, y, item) {
    if(item == undefined || item == null) {
        item = getFreshRenderItem(engine);
    }

    item.img = img;

    let sWidth = engine.relativeGridSize;
    let sHeight = engine.relativeGridSize;

    if(engine.isometricMode) {
        sHeight = engine.halfRelativeGridSize;

        if(img.width != img.height * 2) {
            const rendScale = img.width / engine.relativeGridSize;
            sHeight = img.height / rendScale;
        }

        const iX = (x - y) * engine.halfRelativeGridSize;
        const iY = (x + y) * engine.quarterRelativeGridSize;

        const blX = iX - engine.halfRelativeGridSize;
        const blY = iY + engine.halfRelativeGridSize;

        const dY = blY - sHeight;

        item.x = blX;
        item.y = dY;
        item.w = sWidth;
        item.h = sHeight;

        item.nearness = x + y;
    } else {
        if(img.width != img.height) {
            const rat = img.height / img.width;
            sHeight = engine.relativeGridSize * rat;
        }

        sWidth = Math.ceil(sWidth);
        sHeight = Math.ceil(sHeight);

        const sX = x * engine.relativeGridSize;
        const sY = ((y * engine.relativeGridSize) + engine.relativeGridSize) - sHeight;

        item.x = sX;
        item.y = sY;
        item.w = sWidth;
        item.h = sHeight;
    }

    return item;
}

function getFreshRenderItem(engine) {

    let ri;

    if(usedRenderObjects.length == 0) {
        ri = new RenderItem();
    } else {
        ri = usedRenderObjects.pop();
        ri.x = 0;
        ri.y = 0;
        ri.img = null;
        ri.w = 0;
        ri.h = 0;
        ri.alpha = null;
        ri.isBar = false;
        ri.barWidth = 0;
        ri.meterWidth = 0;
        ri.barColor = "#000000";
        ri.isSquare = false;
        ri.isLine = false;
        ri.isCircle = false;
        ri.color = "#000000";
        ri.nearness = 0;
        ri.tileWidth = 1;
        ri.tileHeight = 1;
        ri.zIndex = 0;
        ri.altitude = 0;
        ri.segmentX = -1;
        ri.cX = 0;
        ri.cY = 0;
        ri.destSegX = 0;
        ri.sW = 0;
        ri.sH = 0;
        ri.blocksLight = false;
        ri.lineWidth = 1;
        ri.angle = 0;
        ri.tX = 0;
        ri.tY = 0;
        ri.dashedLine = false;
        ri.isText = null;
        ri.textFont = null;
    }

    ri.ro = engine.renderOrder;

    engine.renderOrder++;

    return ri;
}

function doDrawSprite(engine, img, x, y, tX, tY, step, meterPercent, meterColor, alpha, zIndex, tileWidth, tileHeight, chevrons, angle, centerChevrons, textLabel, yOffset, scale, textSize, textFont, textYOffset, meterYOffset, elevation) {
    if(!img) {
        return;
    }

    if(engine.fullMapRenderCallback) {
        doDrawTile(engine, img, x, y, zIndex, false, alpha);
        return;
    }

    if(!engine.checkVisibility(x, y)) {
        return;
    }

    engine.instructionsRecieved = true;

    elevation = parseFloat(elevation);

    if(isNaN(elevation)) {
        elevation = 0;
    }

    if(engine.isometricMode && tX == x && tY == y && !engine.useFastRenderMode) {
        return drawBigStationary(engine, img, x, y, tX, tY, step, meterPercent, meterColor, alpha, zIndex, tileWidth, tileHeight, chevrons, angle, centerChevrons, textLabel, yOffset, scale, textSize, textFont, textYOffset, meterYOffset, elevation);
    }

    const item = getFreshRenderItem(engine);

    item.tX = x;
    item.tY = y;

    item.blocksLight = false;
    item.angle = angle;

    item.img = img;
    item.zIndex = zIndex;

    item.tileHeight = tileHeight;
    item.tileWidth = tileWidth;

    item.alpha = alpha;

    let dX, dY;
    let dW = img.width;
    let dH = img.height;

    if(engine.zoomLevel != 1) {
        dW *= engine.zoomLevel;
        dH *= engine.zoomLevel;
    }

    let nearness = y;

    if(engine.isometricMode) {
        const lastTileX = x + tileWidth - 1;
        const lastTileY = y + tileHeight - 1;

        nearness = lastTileX + lastTileY;

        const bottomIsoY = (lastTileX + (lastTileY - yOffset)) * engine.quarterRelativeGridSize;
        const rightIsoX = (lastTileX - (lastTileY - yOffset)) * engine.halfRelativeGridSize;

        const totalBottom = bottomIsoY + engine.halfRelativeGridSize;
        const totalRight = rightIsoX + engine.halfRelativeGridSize;

        dX = totalRight - dW;
        dY = totalBottom - dH;
    } else {
        dX = x * engine.relativeGridSize;
        dY = (((y - yOffset) * engine.relativeGridSize) + engine.relativeGridSize) - dH;
    }

    if(x != tX || y != tY) {
        const stepDistance = engine.twentiethGridSize * step;

        if(engine.isometricMode) {
            let nX = x;
            let nY = y;

            if(tX > x) {
                dX += stepDistance / 2;
                dY += stepDistance / 4;

                nX += 2;
            }

            if(tX < x) {
                dX -= stepDistance / 2;
                dY -= stepDistance / 4;

                nX++;
            }

            if(tY > y) {
                dX -= stepDistance / 2;
                dY += stepDistance / 4;

                nY += 2;
            }

            if(tY < y) {
                dX += stepDistance / 2;
                dY -= stepDistance / 4;

                nY++;
            }

            nearness = nX + nY;
        } else {
            if(tX > x) {
                dX += stepDistance;
            }

            if(tX < x) {
                dX -= stepDistance;
            }

            if(tY > y) {
                dY += stepDistance;
            }

            if(tY < y) {
                dY -= stepDistance;
            }
        }
    }

    if(elevation > 0) {
        produceShadow(engine, x, y, zIndex, tileWidth);
        nearness += elevation;
        dY -= Math.round((elevation & engine.gridSize) * engine.zoomLevel);
    }

    item.x = dX;
    item.y = dY;
    item.w = dW;
    item.h = dH;

    item.nearness = nearness;

    engine.drawQueue.push(item);

    handleMeterAndChevrons(engine, y, dX, dY, dW, dH, meterPercent, meterColor, chevrons, centerChevrons, yOffset, meterYOffset, nearness, zIndex);

    if(textLabel) {
        handleTextLabel(engine, textLabel, textFont, textSize, dX, dY, dW, dH, nearness, zIndex, textYOffset);
    }

    return {
        x: dX,
        y: dY,
        w: dW,
        h: dH
    };
}

function drawBigStationary(engine, img, x, y, tX, tY, step, meterPercent, meterColor, alpha, zIndex, tileWidth, tileHeight, chevrons, angle, centerChevrons, textLabel, yOffset, scale, textSize, textFont, textYOffset, meterYOffset, elevation) {
    let dX, dY;
    let dW = img.width * scale;
    let dH = img.height * scale;

    if(engine.zoomLevel != 1) {
        dW *= engine.zoomLevel;
        dH *= engine.zoomLevel;
    }

    const lastTileX = x + tileWidth - 1;
    const lastTileY = y + tileHeight - 1;

    const bottomIsoY = (lastTileX + (lastTileY - yOffset)) * engine.quarterRelativeGridSize;
    const rightIsoX = (lastTileX - (lastTileY - yOffset)) * engine.halfRelativeGridSize;

    const totalBottom = bottomIsoY + engine.halfRelativeGridSize;
    const totalRight = rightIsoX + engine.halfRelativeGridSize;

    dX = totalRight - dW;
    dY = totalBottom - dH;

    const segmentSize = engine.halfGridSize / scale;

    const drawSegments = Math.round(img.width / segmentSize);

    let segX = 0;
    let dSegX = 0;

    for(let i = 0; i < drawSegments; i++) {
        const item = getFreshRenderItem(engine);

        const segLeftX = dX + (engine.halfRelativeGridSize * i);
        const segRightX = segLeftX + engine.halfRelativeGridSize;

        let nearness = x + y;

        for(let sX = x; sX < x + tileWidth; sX++) {
            for(let sY = y; sY < y + tileHeight; sY++) {
                const isoX = (sX - sY) * engine.halfRelativeGridSize;
                const tDX = isoX - engine.halfRelativeGridSize;

                let right = isoX + engine.halfRelativeGridSize;

                if(right > totalRight) {
                    right = totalRight;
                }

                const tileNearness = sX + sY;

                if(right >= segLeftX && tDX <= segRightX) {
                    if(tileNearness > nearness) {
                        nearness = tileNearness;
                    }
                }
            }
        }

        item.sW = segmentSize;
        item.sH = img.height;

        item.img = img;
        item.zIndex = zIndex;

        if(elevation) {
            if(i == 0) {
                produceShadow(engine, x, y, zIndex, tileWidth);
                dY -= Math.round((elevation & engine.gridSize) * engine.zoomLevel);
            }
            
            nearness += elevation;
        }

        item.cX = x;
        item.cY = y;

        item.x = dX;
        item.y = dY;
        item.w = dW;
        item.h = dH;

        item.tileWidth = tileWidth;
        item.tileHeight = tileHeight;

        item.alpha = alpha;
        item.nearness = nearness;

        item.segmentX = segX;
        item.destSegX = dSegX;

        segX += segmentSize;
        dSegX += engine.halfRelativeGridSize;

        engine.drawQueue.push(item);

        if(i == tileWidth - 1) {
            handleMeterAndChevrons(engine, y, dX, dY, dW, dH, meterPercent, meterColor, chevrons, centerChevrons, yOffset, meterYOffset, nearness, zIndex);
        }
    }

    if(textLabel) {
        handleTextLabel(engine, textLabel, textFont, textSize, dX, dY, dW, dH, x + y, zIndex, textYOffset);
    }

    return {
        x: dX,
        y: dY,
        w: dW,
        h: dH
    };
}

function handleMeterAndChevrons(engine, y, dX, dY, dW, dH, meterPercent, meterColor, chevrons, centerChevrons, yOffset, meterYOffset, nearness, zIndex) {
    let hadBar = false;

    if(meterPercent && meterPercent > 0) {
        hadBar = true;

        const barItem = getFreshRenderItem(engine);

        barItem.isBar = true;
        barItem.x = dX;
        barItem.y = dY + dH;

        if(meterYOffset) {
            barItem.y = ((((y - yOffset) + meterYOffset) * engine.relativeGridSize) + engine.relativeGridSize);
        }

        let mw = dW;

        if(!engine.isometricMode) {
            mw = Math.round(dW * 0.7);
            barItem.x += Math.round(dW * 0.15);
        }

        barItem.barWidth = mw;
        barItem.meterWidth = (mw * meterPercent) - 2;
        barItem.barColor = meterColor;
        barItem.nearness = nearness + 1;

        if(engine.isometricMode) {
            barItem.nearness++;
        }

        barItem.zIndex = zIndex + 1;

        engine.aboveFoldDrawQueue.push(barItem);
    }

    if(chevrons != null) {
        let cPos = dX;
        let yPos = dY + dH;

        if(hadBar) {
            yPos += 10;
        }

        if(centerChevrons) {
            yPos = dY + Math.round(dH / 2);
            yPos -= 5;

            let totalMidPos = 0;

            for(const chevron of chevrons) {
                if(chevron.image) {
                    totalMidPos += 20;
                } else {
                    totalMidPos += 10;
                }
            }

            const hMPos = Math.round(totalMidPos / 2);
            cPos = (dX + Math.round(dW / 2)) - hMPos;
        }

        for(const chevron of chevrons) {
            const chevItem = getFreshRenderItem(engine);

            chevItem.x = cPos;
            chevItem.y = yPos;

            if(chevron.image) {
                chevItem.img = chevron.image;
                chevItem.w = 16;
                chevItem.h = 16;
                chevItem.y -= 5;

                cPos += 10;
            } else {
                chevItem.isBar = true;
                chevItem.barWidth = 6;
                chevItem.meterWidth = 4;
                chevItem.barColor = chevron.color;
            }

            chevItem.nearness = nearness + 1;

            if(engine.isometricMode) {
                chevItem.nearness++;
            }

            chevItem.zIndex = zIndex + 1;

            engine.aboveFoldDrawQueue.push(chevItem);

            cPos += 10;
        }
    }
}

function handleTextLabel(engine, textLabel, textFont, textSize, dX, dY, dW, dH, nearness, zIndex, textYOffset) {
    const textItem = getFreshRenderItem(engine);

    textItem.isText = textLabel;
    textItem.textFont = textFont;
    textItem.lineWidth = textSize;
    textItem.x = dX + Math.round(dW / 2);
    textItem.y = dY + Math.round(dH / 2);
    textItem.color = "#ffffff";
    textItem.barColor = "#000000";

    if(textYOffset) {
        textItem.y += (textYOffset * engine.relativeGridSize);
    }

    textItem.nearness = nearness + 1;

    if(engine.isometricMode) {
        textItem.nearness++;
    }

    textItem.zIndex = zIndex + 1;

    engine.drawQueue.push(textItem);
}

function produceShadow(engine, x, y, zIndex, tileWidth) {
    const shadowItem = getFreshRenderItem(engine);

    let circleNearness = y;

    if(engine.isometricMode) {
        circleNearness += x;
    
        shadowItem.x = (x - y) * engine.halfRelativeGridSize;
        shadowItem.y = (x + y) * engine.quarterRelativeGridSize;
    
        shadowItem.y += engine.quarterRelativeGridSize;
    } else {
        shadowItem.x = (x * engine.relativeGridSize);
        shadowItem.y = (y * engine.relativeGridSize);
    
        shadowItem.x += engine.halfRelativeGridSize;
        shadowItem.y += engine.halfRelativeGridSize;
    }

    shadowItem.isCircle = true;
    shadowItem.color = "rgba(0,0,0,0.25)";
    shadowItem.alpha =1;
    shadowItem.lineWidth = 0;
    shadowItem.zIndex = zIndex;
    shadowItem.h = (tileWidth * engine.relativeGridSize) / 4;
    shadowItem.nearness = circleNearness + 0.1;

    engine.drawQueue.push(shadowItem);
}

function doPopText(engine, x, y, text, color) {
    let popX, popY;

    if(engine.isometricMode) {
        const isoX = (x - y) * engine.halfRelativeGridSize;
        const isoY = (x + y) * engine.quarterRelativeGridSize;

        popX = (isoX - engine.halfRelativeGridSize) + engine.halfRelativeGridSize;

        const bottomLeftY = isoY + engine.halfRelativeGridSize;

        popY = (bottomLeftY - engine.relativeGridSize) + engine.halfRelativeGridSize;
    } else {
        popX = (x * engine.relativeGridSize) + engine.halfRelativeGridSize;
        popY = (y * engine.relativeGridSize) + engine.halfRelativeGridSize;
    }

    let freshPop = null;

    if(usedPopperObjects.length == 0) {
        freshPop = new TextPopItem(popX, popY, text, color);
    } else {
        freshPop = usedPopperObjects.pop();
        freshPop.x = popX;
        freshPop.y = popY;
        freshPop.text = text;
        freshPop.color = color;
        freshPop.cashed = false;
        freshPop.alpha = 1.0;
    }

    engine.textPoppers.push(freshPop);
}

function doDrawSquare(engine, color, x, y, zIndex, composite) {
    if(!engine.drawQueue) {
        return;
    }

    if(!engine.checkVisibility(x, y) && !engine.fullMapRenderCallback) {
        return;
    }

    engine.instructionsRecieved = true;

    let nearness = y;

    const item = getFreshRenderItem(engine);

    item.isSquare = true;
    item.color = color;
    item.img = composite;

    if(engine.isometricMode) {
        nearness += x;

        const isoX = (x - y) * engine.halfRelativeGridSize;
        const isoY = (x + y) * engine.quarterRelativeGridSize;

        item.x = isoX;
        item.y = isoY;
    } else {
        item.x = x * engine.relativeGridSize;
        item.y = y * engine.relativeGridSize;
    }

    item.nearness = nearness;
    item.zIndex = zIndex;

    engine.drawQueue.push(item);
}

function doDrawText(engine, text, x, y, color, stroke, size, font, zIndex) {
    const item = getFreshRenderItem(engine);

    if(engine.isometricMode) {
        item.x = (x - y) * engine.halfRelativeGridSize;
        item.y = (x + y) * engine.quarterRelativeGridSize;
    } else {
        item.x = (x * engine.relativeGridSize) + engine.halfRelativeGridSize;
        item.y = (y * engine.relativeGridSize) + engine.halfRelativeGridSize;
    }

    item.isText = text;
    item.lineWidth = size;
    item.textFont = font;
    item.zIndex = zIndex;

    item.color = color;
    item.barColor = stroke;

    engine.drawQueue.push(item);
}

function processUpdate(engine, timestamp, delta) {
    engine.lightSources = [];

    if(engine.mouseScrolling.up || engine.mouseScrolling.down || engine.mouseScrolling.left || engine.mouseScrolling.right) {
        engine.changed = true;

        if(engine.mouseScrolling.up) {
            engine.viewY -= 40 * delta;
        }

        if(engine.mouseScrolling.down) {
            engine.viewY += 40 * delta;
        }

        if(engine.mouseScrolling.left) {
            engine.viewX -= 40 * delta;
        }

        if(engine.mouseScrolling.right) {
            engine.viewX += 40 * delta;
        }

        engine.checkBounds();
        engine.notifyViewportChange(true);
    }

    engine.gamepadNegotiationTimer += delta;

    if(engine.gamepadNegotiationTimer >= 4) {
        engine.gamepadNegotiationTimer = 0;
        performGamepadUpdate(engine);
    }

    if(!engine.updateFunction) {
        return;
    }

    let updateDiff = 0;

    if(isNaN(engine.lastUpdateUpdate)) {
        updateDiff = 1000;
    } else {
        updateDiff = timestamp - engine.lastUpdateUpdate;
    }

    const logicDelta = updateDiff / engine.updateTime;

    if(updateDiff >= engine.updateTime) {
        engine.lastUpdateUpdate = timestamp;
        engine.updateFunction(timestamp, logicDelta);
    }
}

function performGamepadUpdate(engine) {
    let didHover = false;

    if(engine.padScrolling.up && !engine.padScrolling.down && !engine.padScrolling.left && !engine.padScrolling.right) {
        engine.lastHoverY--;

        if(engine.isometricMode) {
            engine.lastHoverX--;
        }

        didHover = true;
    }

    if(engine.padScrolling.down && !engine.padScrolling.up && !engine.padScrolling.left && !engine.padScrolling.right) {
        engine.lastHoverY++;

        if(engine.isometricMode) {
            engine.lastHoverX++;
        }

        didHover = true;
    }

    if(engine.padScrolling.left && !engine.padScrolling.right && !engine.padScrolling.up && !engine.padScrolling.down) {
        engine.lastHoverX--;

        if(engine.isometricMode) {
            engine.lastHoverY++;
        }

        didHover = true;
    }

    if(engine.padScrolling.right && !engine.padScrolling.left && !engine.padScrolling.up && !engine.padScrolling.down) {
        engine.lastHoverX++;

        if(engine.isometricMode) {
            engine.lastHoverY--;
        }

        didHover = true;
    }

    if(engine.padScrolling.up && !engine.padScrolling.down && !engine.padScrolling.left && engine.padScrolling.right) {
        engine.lastHoverY--;

        if(engine.isometricMode) {
            engine.lastHoverX++;
        }

        didHover = true;
    }

    if(engine.padScrolling.down && !engine.padScrolling.up && !engine.padScrolling.left && engine.padScrolling.right) {
        engine.lastHoverY++;

        if(engine.isometricMode) {
            engine.lastHoverX--;
        }

        didHover = true;
    }

    if(engine.padScrolling.left && !engine.padScrolling.right && !engine.padScrolling.up && engine.padScrolling.down) {
        engine.lastHoverX--;

        if(engine.isometricMode) {
            engine.lastHoverY--;
        }

        didHover = true;
    }

    if(engine.padScrolling.right && !engine.padScrolling.left && !engine.padScrolling.up && engine.padScrolling.down) {
        engine.lastHoverX++;

        if(engine.isometricMode) {
            engine.lastHoverY++;
        }

        didHover = true;
    }

    if(didHover && engine.hoverFunction) {
        engine.hoverFunction(engine.lastHoverX, engine.lastHoverY, 0, 0, "gamepad", engine.lastHoverX, engine.lastHoverY);
        engine.centerOnCoord(engine.lastHoverX, engine.lastHoverY);
    }

    let didScroll = false;

    if(engine.padRightScrolling.left) {
        engine.viewX -= 40;
        didScroll = true;
    }

    if(engine.padRightScrolling.right) {
        engine.viewX += 40;
        didScroll = true;
    }

    if(engine.padRightScrolling.up) {
        engine.viewY -= 40;
        didScroll = true;
    }

    if(engine.padRightScrolling.down) {
        engine.viewY += 40;
        didScroll = true;
    }

    if(didScroll) {
        engine.changed();
        engine.notifyViewportChange(true);
        engine.checkBounds();
    }

    if(engine.padTriggers.right && !engine.padTriggers.left) {
        engine.doZoom(true);
    }

    if(engine.padTriggers.left && !engine.padTriggers.right) {
        engine.doZoom(false);
    }
}

function doDrawLine(engine, color, x, y, x2, y2, zIndex, centerInTile, lineWidth, dashed) {
    if(!engine.drawQueue) {
        return;
    }

    engine.instructionsRecieved = true;

    const nearness = (x * 2) + (y * 2) + zIndex;

    const item = getFreshRenderItem(engine);

    item.isLine = true;
    item.color = color;
    item.alpha = 1;
    item.lineWidth = lineWidth;
    item.zIndex = zIndex;
    item.dashedLine = dashed;

    if(engine.isometricMode) {
        const l1x = (x - y) * engine.halfRelativeGridSize;
        const l1y = (x + y) * engine.quarterRelativeGridSize;

        const l2x = (x2 - y2) * engine.halfRelativeGridSize;
        const l2y = (x2 + y2) * engine.quarterRelativeGridSize;

        item.x = l1x;
        item.y = l1y;

        item.w = l2x;
        item.h = l2y;

        if(centerInTile) {
            item.y += engine.quarterRelativeGridSize;
            item.h += engine.quarterRelativeGridSize;
        }
    } else {
        item.x = x * engine.relativeGridSize;
        item.y = y * engine.relativeGridSize;

        item.w = x2 * engine.relativeGridSize;
        item.h = y2 * engine.relativeGridSize;

        if(centerInTile) {
            item.x += engine.halfRelativeGridSize;
            item.y += engine.halfRelativeGridSize;
            item.w += engine.halfRelativeGridSize;
            item.h += engine.halfRelativeGridSize;
        }
    }

    item.nearness = nearness;

    engine.drawQueue.push(item);
}

function doDrawCircle(engine, color, x, y, tileRadius, zIndex, lineWidth, dashed) {
    
    const item = getFreshRenderItem(engine);

    item.isCircle = true;
    item.color = color;
    item.alpha = 1;
    item.lineWidth = lineWidth;
    item.zIndex = zIndex;
    item.dashedLine = dashed;

    item.h = (tileRadius * engine.relativeGridSize) / 2;
    
    let nearness = y;

    if(engine.isometricMode) {
        nearness += x;

        item.x = (x - y) * engine.halfRelativeGridSize;
        item.y = (x + y) * engine.quarterRelativeGridSize;

        item.y += engine.quarterRelativeGridSize;
    } else {
        item.x = x * engine.relativeGridSize;
        item.y = y * engine.relativeGridSize;

        item.x += engine.halfRelativeGridSize;
        item.y += engine.halfRelativeGridSize;
    }

    item.nearness = nearness + 0.56;

    engine.drawQueue.push(item);
}

function getGroupRegionLines(tilesArray) {
    let i,j,ti,tj,dTop,dRight,dBottom,dLeft;

    const linesToDraw = [];

    for(i = 0; i < tilesArray.length; i++) {
        ti = tilesArray[i];

        dTop = true;
        dRight = true;
        dBottom = true;
        dLeft = true;

        for(j = 0; j < tilesArray.length; j++) {
            tj = tilesArray[j];

            if(ti == tj) {
                continue;
            }

            if(ti.x == tj.x) {
                if(tj.y == ti.y - 1) {
                    dTop = false;
                }

                if(tj.y == ti.y + 1) {
                    dBottom = false;
                }
            }

            if(ti.y == tj.y) {
                if(tj.x == ti.x - 1) {
                    dLeft = false;
                }

                if(tj.x == ti.x + 1) {
                    dRight = false;
                }
            }
        }

        if(dTop) {
            linesToDraw.push({
                x1: ti.x,
                y1: ti.y,
                x2: ti.x + 1,
                y2: ti.y
            });
        }

        if(dRight) {
            linesToDraw.push({
                x1: ti.x + 1,
                y1: ti.y,
                x2: ti.x + 1,
                y2: ti.y + 1
            });
        }

        if(dBottom) {
            linesToDraw.push({
                x1: ti.x,
                y1: ti.y + 1,
                x2: ti.x + 1,
                y2: ti.y + 1
            });
        }

        if(dLeft) {
            linesToDraw.push({
                x1: ti.x,
                y1: ti.y,
                x2: ti.x,
                y2: ti.y + 1
            });
        }
    }

    return linesToDraw;
}

function onGamepadDown(engine, button) {
    if(button == "lt") {
        engine.padTriggers.left = true;
    }

    if(button == "rt") {
        engine.padTriggers.right = true;
    }

    if(button == "up") {
        engine.padScrolling.up = true;
        engine.padScrolling.down = false;
    }

    if(button == "down") {
        engine.padScrolling.down = true;
        engine.padScrolling.up = false;
    }

    if(button == "left") {
        engine.padScrolling.left = true;
        engine.padScrolling.right = false;
    }

    if(button == "right") {
        engine.padScrolling.right = true;
        engine.padScrolling.left = false;
    }

    if(button == "rup") {
        engine.padRightScrolling.up = true;
    }

    if(button == "rdown") {
        engine.padRightScrolling.down = true;
    }

    if(button == "rleft") {
        engine.padRightScrolling.left = true;
    }

    if(button == "rright") {
        engine.padRightScrolling.right = true;
    }

    if(button == "a") {
        engine.aDownTime = new Date().getTime();
    }
}

function onGamepadUp(engine, button) {
    if(button == "lt") {
        engine.padTriggers.left = false;
    }

    if(button == "rt") {
        engine.padTriggers.right = false;
    }

    if(button == "up") {
        engine.padScrolling.up = false;
    }

    if(button == "down") {
        engine.padScrolling.down = false;
    }

    if(button == "left") {
        engine.padScrolling.left = false;
    }

    if(button == "right") {
        engine.padScrolling.right = false;
    }

    if(button == "rup") {
        engine.padRightScrolling.up = false;
    }

    if(button == "rdown") {
        engine.padRightScrolling.down = false;
    }

    if(button == "rleft") {
        engine.padRightScrolling.left = false;
    }

    if(button == "rright") {
        engine.padRightScrolling.right = false;
    }

    if(button == "a") {
        const aUpTime = new Date().getTime();

        if(aUpTime - engine.aDownTime < 400 && engine.clickFunction) {
            engine.clickFunction(engine.lastHoverX, engine.lastHoverY, 0, 0, "gamepad", engine.lastHoverX, engine.lastHoverY);
        }

        engine.aDownTime = 0;
    }
}

function doDrawLight(engine, x, y, radius, color, tX, tY, step, intensity) {
    if(!engine.checkVisibility(x, y) && !engine.fullMapRenderCallback) {
        return;
    }

    const rgbColor = hexToRGB(color);
    const useRadius = radius * engine.relativeGridSize;
    
    let ux = x;
    let uy = y;

    if(engine.isometricMode) {
        ux = (x - y) * engine.halfRelativeGridSize;
        uy = (x + y) * engine.quarterRelativeGridSize;
    } else {
        ux = x * engine.relativeGridSize;
        uy = ((y * engine.relativeGridSize) + engine.relativeGridSize) - engine.halfRelativeGridSize;
    }

    if(x != tX || y != tY) {
        const stepDistance = engine.twentiethGridSize * step;

        if(engine.isometricMode) {
            if(tX > x) {
                ux += stepDistance / 2;
                uy += stepDistance / 4;
            }

            if(tX < x) {
                ux -= stepDistance / 2;
                uy -= stepDistance / 4;
            }

            if(tY > y) {
                ux -= stepDistance / 2;
                uy += stepDistance / 4;
            }

            if(tY < y) {
                ux += stepDistance / 2;
                uy -= stepDistance / 4;
            }
        } else {
            if(tX > x) {
                ux += stepDistance;
            }

            if(tX < x) {
                ux -= stepDistance;
            }

            if(tY > y) {
                uy += stepDistance;
            }

            if(tY < y) {
                uy -= stepDistance;
            }
        }
    }

    engine.lightSources.push(getFreshLightInstruction(ux, uy, useRadius, rgbColor, intensity));
}

function getFreshLightInstruction(x,y,r,c,i) {
    if(lightInstructionRecycling.length > 0) {
        const fresh = lightInstructionRecycling.pop();
        fresh.x = x;
        fresh.y = y;
        fresh.radius = r;
        fresh.color = c;
        fresh.intensity = i;
        return fresh;
    } else {
        return new LightInstruction(x, y, r, c, i);
    }
}

export function pixelateCanvas(canvas) {
    canvas.style.imageRendering = "pixelated";
    
    const ctx = canvas.getContext("2d");
    ctx.imageSmoothingEnabled = false;
    ctx.mozImageSmoothingEnabled = false;
    ctx.webkitImageSmoothingEnabled = false;
    ctx.msImageSmoothingEnabled = false;
}

export default {
    getInstance,
    globalResize,
    hexToRgb,
    Scroll2dEngine,
    Chevron,
    pixelateCanvas
};

requestAnimationFrame(globalRender);