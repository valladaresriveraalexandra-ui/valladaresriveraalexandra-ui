"""
RAE – Registro de Asistencia Estudiantil (versión web con NiceGUI)
====================================================================
Port completo de la versión de escritorio (Tkinter) a NiceGUI, con
todas las funciones de las pestañas de Portería y Administración.

Requisitos:
    pip install nicegui opencv-python face_recognition numpy

Ejecutar con:
    python3 app.py

Notas de diseño:
- La cámara se maneja del lado del servidor (igual que en la versión
  Tkinter), pensado para correr como "kiosco" en la PC de portería.
- Cuando se navega desde "/" hacia login/portería/admin, la cámara de
  reconocimiento en vivo se libera automáticamente para que el
  formulario de "Añadir/Editar estudiante" pueda usarla en exclusiva
  para capturar el rostro.
- La función "Imprimir" del historial se adaptó a "Generar reporte
  (descargar)": en un navegador no se puede mandar a imprimir
  directamente a una impresora del sistema, así que se genera un
  archivo de texto descargable que luego se puede abrir e imprimir.

CAMBIOS EN ESTA VERSIÓN:
- Los IDs de los estudiantes ahora se pueden reorganizar para que
  queden siempre consecutivos (1,2,3,4...) sin huecos, sin importar
  cuántos estudiantes se hayan eliminado. Esto ocurre automáticamente
  al arrancar el programa y cada vez que se elimina un estudiante, y
  también hay un botón manual "Reorganizar IDs" en Gestión de
  Estudiantes por si se necesita forzarlo.
- La puntualidad de salida ahora tiene 3 estados en vez de 2:
    🟠 Salida anticipada  -> se fue antes de las 12:00 PM
    🟢 A tiempo            -> se fue exactamente a las 12:00 PM
    🔵 Salida tardía       -> se fue después de las 12:00 PM
  Antes, cualquier salida después de las 12:00 PM (incluso a las
  8:00 PM) se marcaba como "A tiempo", lo cual era engañoso. Este
  cambio aplica automáticamente en Portería, Historial y Reportes,
  porque todos usan la misma función evaluar_puntualidad_salida().
- El horario de registro sigue siendo 7:00 AM (límite de entrada) a
  12:00 PM (límite de salida); ese horario ahora se refleja de forma
  consistente y correcta en la pestaña "Consultar historial".
- El reconocimiento facial en vivo es más rápido: se redujeron los
  frames necesarios para confirmar una identificación, se bajó el
  tiempo de la barra de verificación, se usa una imagen más pequeña
  para detectar rostros y se limita la resolución de la cámara.
- CORRECCIÓN: En el desplegable de "Registrar un permiso" (panel de
  Reportes), los estudiantes ahora se muestran ordenados por ID
  (ascendente) en lugar de por nombre, para que el orden coincida
  con la numeración esperada (1,2,3,4,5,6,7...).
- NUEVO: Ahora, al hacer clic en los botones de acceso a Portería o
  Administración desde la pantalla principal, se forza el cierre de
  cualquier sesión anterior, por lo que siempre se pedirán las
  credenciales de acceso. Además, la página de login siempre muestra
  el formulario, sin redirigir automáticamente si ya hay sesión.
- MEJORA: El botón "Generar reporte (descargar)" ahora muestra un
  diálogo con un reporte en formato tabla, centrado y con estilo
  profesional, y al abrirlo se ejecuta automáticamente la impresión
  del navegador (window.print()).
- CORRECCIÓN DE IMPRESIÓN: el reporte se generaba con las etiquetas
  <html>/<head>/<body> anidadas dentro de la tarjeta del diálogo, lo
  que hacía que el navegador ignorara los estilos (por eso salía todo
  pegado y sin espacio). Ahora el HTML del reporte es un fragmento
  válido con su propio <style> y se imprime en una ventana aparte,
  limpia, sin el botón "Cerrar" ni el texto "FIN DEL REPORTE".
- CORRECCIÓN DE CODIFICACIÓN (tildes/eñes salían como símbolos raros
  al imprimir, ej. "TÃ©CNICO"): el HTML se mandaba a la ventana nueva
  con atob() + document.write(), y atob() devuelve una cadena binaria
  "byte a byte" que document.write() escribe tal cual como texto
  UTF-16, sin volver a interpretar esos bytes como UTF-8. Resultado:
  cada tilde/eñe se partía en dos caracteres corruptos. Ahora se
  decodifica explícitamente como UTF-8 con TextDecoder antes de
  escribir el documento, así que tildes, eñes y símbolos salen
  perfectos.
- MEJORA DE REPORTE: se quitaron los emojis de la tabla del reporte
  (dependían de fuentes de emoji que no siempre están disponibles al
  imprimir/generar PDF, por eso salían como cuadros "ð..."); ahora la
  puntualidad se muestra con una etiqueta de color (verde/naranja/
  azul/rojo) con texto normal, mucho más legible e imprimible.
- MEJORA DE REPORTE: el encabezado de cada estudiante ahora muestra
  claramente Nombre, ID y Código en líneas/etiquetas separadas y bien
  legibles (antes salía todo pegado en una sola línea pequeña).
- MEJORA DE REPORTE: la tabla ya no lista cada movimiento por
  separado; ahora cada fila es un día con columnas "Hora de Entrada"
  y "Hora de Salida", y una columna "Motivo / Puntualidad de salida"
  que indica si salió con permiso (y el motivo), si salió antes de
  tiempo, a tiempo, o tarde.
"""

import asyncio
import base64
import csv
import io
import pickle
import smtplib
import sqlite3
import threading
import time
from collections import defaultdict
from datetime import datetime
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText

import cv2
import face_recognition

from nicegui import app, ui

# ==================== CONFIGURACIÓN DE CORREO ====================
SMTP_CONFIG = {
    "host": "smtp.gmail.com",
    "port": 587,
    "user": "raeinstituto@gmail.com",
    "password": "ulhr dmfr zoby fjcl",
}
INSTITUCION_NOMBRE = "INSTITUTO NACIONAL TÉCNICO INDUSTRIAL"
CORREO_REPORTES = "riverale610@gmail.com"

# ==================== CONSTANTES ====================
DB_FILE = "proyecto20.db"
HORA_LIMITE_ENTRADA = "07:00 AM"
HORA_LIMITE_SALIDA = "12:00 PM"

# Reconocimiento facial: menos frames de confirmación = respuesta más
# rápida (antes eran 3). 2 sigue siendo suficiente para evitar falsos
# positivos por un solo frame ruidoso.
FRAMES_CONFIRMACION_AUTO = 2
# Antes 2.0s: se acorta la barra de verificación para que el proceso
# completo (detectar -> confirmar -> registrar) se sienta más ágil.
DURACION_VERIFICACION = 1.0
DURACION_MENSAJE_EXITO = 1.2    # segundos que se muestra el mensaje de éxito

STORAGE_SECRET = "cambia-esta-clave-secreta-rae"  # cambiar en producción


# ==================== PUNTUALIDAD ====================
def _parsear_hora(hora_str):
    if not hora_str:
        return None
    try:
        return datetime.strptime(hora_str.strip(), "%I:%M %p")
    except Exception:
        return None


def evaluar_puntualidad_entrada(hora_str):
    h = _parsear_hora(hora_str)
    limite = _parsear_hora(HORA_LIMITE_ENTRADA)
    if h is None or limite is None:
        return "—"
    return "🔴 Tarde" if h.time() > limite.time() else "🟢 A tiempo"


def evaluar_puntualidad_salida(hora_str):
    """Evalúa la hora de salida contra el límite (12:00 PM) y devuelve
    uno de tres estados:
      - 🟠 Salida anticipada : se fue ANTES de la hora límite
      - 🟢 A tiempo           : se fue EXACTAMENTE a la hora límite
      - 🔵 Salida tardía      : se fue DESPUÉS de la hora límite
    """
    h = _parsear_hora(hora_str)
    limite = _parsear_hora(HORA_LIMITE_SALIDA)
    if h is None or limite is None:
        return "—"
    if h.time() < limite.time():
        return "🟠 Salida anticipada"
    elif h.time() > limite.time():
        return "🔵 Salida tardía"
    else:
        return "🟢 A tiempo"


# ==================== BASE DE DATOS ====================
def get_connection():
    return sqlite3.connect(DB_FILE)


def reorganizar_ids_estudiantes():
    """Renumera los IDs de los estudiantes para que queden siempre
    consecutivos (1, 2, 3, 4, ...) sin huecos, sin importar cuántos se
    hayan eliminado con el paso del tiempo. Actualiza también las
    referencias en 'registros' y 'estudiantes_faces', y reinicia el
    contador AUTOINCREMENT para que el próximo estudiante nuevo
    continúe justo después del último ID en uso.

    Devuelve la cantidad de estudiantes cuyo ID cambió.
    """
    conn = get_connection()
    c = conn.cursor()
    c.execute("SELECT id FROM estudiantes ORDER BY id ASC")
    ids_actuales = [row[0] for row in c.fetchall()]

    cambios = 0
    # Procesar en orden ascendente: como el nuevo_id siempre es menor
    # o igual al viejo_id, nunca hay choques de clave primaria al
    # reasignar (el hueco que deja cada reasignación siempre queda
    # "por delante" de los IDs que aún no se han procesado).
    for nuevo_id, viejo_id in enumerate(ids_actuales, start=1):
        if nuevo_id != viejo_id:
            c.execute("UPDATE estudiantes SET id=? WHERE id=?", (nuevo_id, viejo_id))
            c.execute("UPDATE registros SET estudiante_id=? WHERE estudiante_id=?", (nuevo_id, viejo_id))
            c.execute("UPDATE estudiantes_faces SET estudiante_id=? WHERE estudiante_id=?", (nuevo_id, viejo_id))
            cambios += 1

    max_id = len(ids_actuales)
    c.execute("SELECT COUNT(*) FROM sqlite_sequence WHERE name='estudiantes'")
    if c.fetchone()[0]:
        c.execute("UPDATE sqlite_sequence SET seq=? WHERE name='estudiantes'", (max_id,))
    else:
        c.execute("INSERT INTO sqlite_sequence (name, seq) VALUES ('estudiantes', ?)", (max_id,))

    conn.commit()
    conn.close()
    return cambios


def init_db():
    conn = get_connection()
    c = conn.cursor()
    c.execute("""
        CREATE TABLE IF NOT EXISTS estudiantes (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            nombre   TEXT NOT NULL,
            apellido TEXT NOT NULL,
            grado    TEXT NOT NULL,
            password TEXT NOT NULL DEFAULT '1234',
            email_encargado TEXT
        )
    """)
    try:
        c.execute("ALTER TABLE estudiantes ADD COLUMN email_encargado TEXT")
    except sqlite3.OperationalError:
        pass

    c.execute("""
        CREATE TABLE IF NOT EXISTS registros (
            id              INTEGER PRIMARY KEY AUTOINCREMENT,
            estudiante_id   INTEGER NOT NULL,
            tipo            TEXT NOT NULL,
            fecha           TEXT NOT NULL,
            hora            TEXT NOT NULL,
            observaciones   TEXT,
            registrado_por  TEXT DEFAULT 'Sistema',
            FOREIGN KEY (estudiante_id) REFERENCES estudiantes(id)
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS usuarios (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            usuario  TEXT UNIQUE NOT NULL,
            password TEXT NOT NULL,
            rol      TEXT NOT NULL
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS estudiantes_faces (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            estudiante_id INTEGER NOT NULL,
            encoding      BLOB NOT NULL,
            FOREIGN KEY (estudiante_id) REFERENCES estudiantes(id) ON DELETE CASCADE
        )
    """)

    c.execute("SELECT COUNT(*) FROM estudiantes")
    if c.fetchone()[0] == 0:
        c.executemany(
            "INSERT INTO estudiantes (nombre, apellido, grado, password, email_encargado) VALUES (?,?,?,?,?)",
            [("Juan", "Pérez", "5to", "1234", "juan@correo.com"),
             ("María", "García", "6to", "1234", "maria@correo.com"),
             ("Carlos", "Rodríguez", "5to", "1234", "carlos@correo.com")]
        )
    c.execute("SELECT COUNT(*) FROM usuarios")
    if c.fetchone()[0] == 0:
        c.executemany(
            "INSERT INTO usuarios (usuario, password, rol) VALUES (?,?,?)",
            [("porteria", "1234", "porteria"), ("admin", "admin", "admin")]
        )
    conn.commit()
    conn.close()

    # Arreglar automáticamente cualquier ID de estudiante con huecos
    # que haya quedado de versiones anteriores (por ejemplo 1,2,5,6,7,9,10).
    reorganizar_ids_estudiantes()


# ==================== ENVÍO DE CORREOS ====================
def enviar_correo(para, asunto, cuerpo):
    try:
        msg = MIMEMultipart()
        msg['From'] = SMTP_CONFIG['user']
        msg['To'] = para
        msg['Subject'] = asunto
        msg.attach(MIMEText(cuerpo, 'plain', 'utf-8'))
        server = smtplib.SMTP(SMTP_CONFIG['host'], SMTP_CONFIG['port'])
        server.starttls()
        server.login(SMTP_CONFIG['user'], SMTP_CONFIG['password'])
        server.send_message(msg)
        server.quit()
        return True
    except Exception as e:
        print(f"Error al enviar correo: {e}")
        return False


def enviar_correo_permiso(estudiante_nombre, fecha, hora, correo_encargado, motivo=None):
    if not correo_encargado:
        return False
    asunto = f"Notificación de permiso - {INSTITUCION_NOMBRE}"
    motivo_texto = motivo if motivo else "No especificado"
    cuerpo = f"""
Estimado encargado,

Se le informa que el estudiante {estudiante_nombre} ha solicitado un permiso de salida de la institución.

Fecha: {fecha}
Hora: {hora}
Motivo: {motivo_texto}

Este permiso fue registrado en el sistema de asistencia de {INSTITUCION_NOMBRE}.

Atentamente,
Sistema de Registro de Asistencia Estudiantil (RAE)
{INSTITUCION_NOMBRE}
    """
    return enviar_correo(correo_encargado, asunto, cuerpo)


def enviar_correo_entrada_tardia(estudiante_nombre, fecha, hora, correo_encargado):
    if not correo_encargado:
        return False
    asunto = f"Entrada tardía - {INSTITUCION_NOMBRE}"
    cuerpo = f"""
Estimado encargado,

Se le informa que el estudiante {estudiante_nombre} ha registrado una entrada tardía hoy {fecha} a las {hora}.

La hora límite de entrada es {HORA_LIMITE_ENTRADA}.

Atentamente,
Sistema de Registro de Asistencia Estudiantil (RAE)
{INSTITUCION_NOMBRE}
    """
    return enviar_correo(correo_encargado, asunto, cuerpo)


def enviar_correo_salida_anticipada(estudiante_nombre, fecha, hora, correo_encargado):
    if not correo_encargado:
        return False
    asunto = f"Salida anticipada - {INSTITUCION_NOMBRE}"
    cuerpo = f"""
Estimado encargado,

Se le informa que el estudiante {estudiante_nombre} ha registrado una salida anticipada hoy {fecha} a las {hora}.

La hora límite de salida es {HORA_LIMITE_SALIDA}.

Atentamente,
Sistema de Registro de Asistencia Estudiantil (RAE)
{INSTITUCION_NOMBRE}
    """
    return enviar_correo(correo_encargado, asunto, cuerpo)


def enviar_correo_salida_tardia(estudiante_nombre, fecha, hora, correo_encargado):
    if not correo_encargado:
        return False
    asunto = f"Salida tardía - {INSTITUCION_NOMBRE}"
    cuerpo = f"""
Estimado encargado,

Se le informa que el estudiante {estudiante_nombre} registró su salida hoy {fecha} a las {hora}, después de la hora límite de salida ({HORA_LIMITE_SALIDA}).

Atentamente,
Sistema de Registro de Asistencia Estudiantil (RAE)
{INSTITUCION_NOMBRE}
    """
    return enviar_correo(correo_encargado, asunto, cuerpo)


# ==================== REGISTRO PRINCIPAL DE ASISTENCIA ====================
def realizar_registro_db(est_id, nombre, apellido, tipo_override=None):
    """Inserta el movimiento (Ingreso/Salida/Permiso) en la BD, envía
    correos de alerta si corresponde, y devuelve (tipo, nombre, apellido, puntualidad).
    No dispara notificaciones de UI: eso lo hace quien la llama."""
    now = datetime.now()
    fecha = now.strftime("%Y-%m-%d")
    hora = now.strftime("%I:%M %p")
    conn = get_connection()
    c = conn.cursor()

    if tipo_override:
        tipo = tipo_override
    else:
        c.execute(
            "SELECT tipo FROM registros WHERE estudiante_id=? AND fecha=? ORDER BY id DESC LIMIT 1",
            (est_id, fecha)
        )
        ultimo = c.fetchone()
        tipo = "Salida" if ultimo and ultimo[0] in ("Ingreso", "Permiso") else "Ingreso"

    if tipo == "Ingreso":
        puntualidad = evaluar_puntualidad_entrada(hora)
    elif tipo == "Permiso":
        puntualidad = "🟢 Con permiso"
    else:
        puntualidad = evaluar_puntualidad_salida(hora)

    observacion = f"Registrado automáticamente — {puntualidad}"
    c.execute(
        "INSERT INTO registros (estudiante_id, tipo, fecha, hora, observaciones) VALUES (?,?,?,?,?)",
        (est_id, tipo, fecha, hora, observacion)
    )
    conn.commit()

    c.execute("SELECT email_encargado FROM estudiantes WHERE id=?", (est_id,))
    row_email = c.fetchone()
    email_encargado = row_email[0] if row_email else None

    if email_encargado:
        nombre_completo = f"{nombre} {apellido}"
        if tipo == "Ingreso" and "Tarde" in puntualidad:
            enviar_correo_entrada_tardia(nombre_completo, fecha, hora, email_encargado)
        elif tipo == "Salida" and "Salida anticipada" in puntualidad:
            enviar_correo_salida_anticipada(nombre_completo, fecha, hora, email_encargado)
        elif tipo == "Salida" and "Salida tardía" in puntualidad:
            enviar_correo_salida_tardia(nombre_completo, fecha, hora, email_encargado)

    conn.close()
    return tipo, nombre, apellido, puntualidad


def _color_notify_por_tipo(tipo):
    return 'positive' if tipo == "Ingreso" else ('warning' if tipo == "Permiso" else 'info')


def _emoji_por_tipo(tipo):
    return "✅" if tipo == "Ingreso" else ("📝" if tipo == "Permiso" else "🚪")


# ==================== MOTOR DE RECONOCIMIENTO EN VIVO (pantalla principal) ====================
class MotorReconocimientoVivo:
    """Cámara continua para la pantalla de inicio: reconoce rostros y,
    tras N frames de confirmación, deja el resultado en `pending` para
    que la UI (en el hilo de eventos de NiceGUI) lo procese."""

    def __init__(self):
        self.cap = None
        self.running = False
        self.lock = threading.Lock()
        self.thread = None

        self.known_encodings = []
        self.known_ids = []
        self.known_names = []

        self.current_jpeg = None
        self.estado_texto = "Iniciando cámara..."
        self.bloqueado = False
        self.pending = None  # (est_id, nombre, apellido)

        self._frames_confirm = 0
        self._ultimo_id = None

    def cargar_codificaciones(self):
        encodings, ids, names = [], [], []
        conn = get_connection()
        c = conn.cursor()
        c.execute("""
            SELECT f.estudiante_id, f.encoding, e.nombre||' '||e.apellido
            FROM estudiantes_faces f
            JOIN estudiantes e ON f.estudiante_id = e.id
        """)
        for est_id, blob, nombre in c.fetchall():
            try:
                encodings.append(pickle.loads(blob))
                ids.append(est_id)
                names.append(nombre)
            except Exception:
                pass
        conn.close()
        with self.lock:
            self.known_encodings = encodings
            self.known_ids = ids
            self.known_names = names

    def iniciar(self):
        if self.running:
            return True
        self.cargar_codificaciones()
        self.cap = cv2.VideoCapture(0, cv2.CAP_DSHOW) if hasattr(cv2, 'CAP_DSHOW') else cv2.VideoCapture(0)
        if not self.cap.isOpened():
            self.cap = None
            self.estado_texto = "⚠ No se pudo abrir la cámara. Use el ID manual."
            return False
        # Limitar la resolución de captura acelera la detección de
        # rostros por frame (menos píxeles que procesar).
        self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, 640)
        self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 480)
        try:
            self.cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
        except Exception:
            pass
        self.running = True
        self.bloqueado = False
        self.estado_texto = "🔍 Buscando rostro..."
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()
        return True

    def detener(self):
        self.running = False
        if self.thread is not None:
            self.thread.join(timeout=1.5)
            self.thread = None
        if self.cap is not None:
            try:
                self.cap.release()
            except Exception:
                pass
            self.cap = None
        self.current_jpeg = None

    def desbloquear(self):
        self.bloqueado = False
        self.pending = None
        self._ultimo_id = None
        self._frames_confirm = 0

    def _loop(self):
        # Escala más pequeña (antes 0.25) = menos píxeles a analizar
        # por frame = detección más rápida.
        scale = 0.20
        while self.running:
            if self.cap is None:
                break
            ret, frame = self.cap.read()
            if not ret:
                time.sleep(0.05)
                continue
            frame = cv2.flip(frame, 1)

            if not self.bloqueado:
                small = cv2.resize(frame, (0, 0), fx=scale, fy=scale)
                rgb_small = cv2.cvtColor(small, cv2.COLOR_BGR2RGB)
                locs = face_recognition.face_locations(
                    rgb_small, number_of_times_to_upsample=0, model='hog'
                )
                encs = face_recognition.face_encodings(rgb_small, locs, num_jitters=0)

                nombre_disp = "Desconocido"
                color = (0, 0, 255)
                reconocido = None

                with self.lock:
                    known_encodings = list(self.known_encodings)
                    known_ids = list(self.known_ids)
                    known_names = list(self.known_names)

                for enc in encs:
                    if known_encodings:
                        matches = face_recognition.compare_faces(known_encodings, enc, tolerance=0.5)
                        if True in matches:
                            idx = matches.index(True)
                            nombre_disp = known_names[idx]
                            reconocido = (known_ids[idx], known_names[idx])
                            color = (0, 255, 0)
                            break

                for (top, right, bottom, left) in locs:
                    top = int(top / scale)
                    right = int(right / scale)
                    bottom = int(bottom / scale)
                    left = int(left / scale)
                    cv2.rectangle(frame, (left, top), (right, bottom), color, 2)
                    cv2.putText(frame, nombre_disp, (left, top - 10),
                                cv2.FONT_HERSHEY_SIMPLEX, 0.7, color, 2)

                if reconocido:
                    est_id = reconocido[0]
                    if est_id == self._ultimo_id:
                        self._frames_confirm = min(self._frames_confirm + 1, FRAMES_CONFIRMACION_AUTO)
                    else:
                        self._ultimo_id = est_id
                        self._frames_confirm = 1

                    self.estado_texto = f"✅ Reconocido: {nombre_disp}"

                    if self._frames_confirm >= FRAMES_CONFIRMACION_AUTO:
                        self._frames_confirm = 0
                        self.bloqueado = True
                        partes = nombre_disp.split(" ", 1)
                        nom = partes[0]
                        ape = partes[1] if len(partes) > 1 else ""
                        self.pending = (est_id, nom, ape)
                else:
                    self._ultimo_id = None
                    self._frames_confirm = 0
                    self.estado_texto = "🔍 Buscando rostro..."

            ret2, jpeg = cv2.imencode('.jpg', frame)
            if ret2:
                with self.lock:
                    self.current_jpeg = jpeg.tobytes()
            # Antes 0.03s (~33fps máx). Bajarlo deja que el hilo intente
            # leer/procesar frames con más frecuencia.
            time.sleep(0.015)

    def get_frame(self):
        with self.lock:
            return self.current_jpeg


motor = MotorReconocimientoVivo()


# ==================== CÁMARA DE CAPTURA (formulario de estudiante) ====================
class CapturaCamara:
    """Cámara dedicada, de un solo uso, para capturar el encoding facial
    de un estudiante nuevo o para actualizar el de uno existente."""

    def __init__(self):
        self.cap = None
        self.running = False
        self.lock = threading.Lock()
        self.thread = None
        self.current_jpeg = None
        self.last_frame = None

    def iniciar(self):
        if self.running:
            return True
        self.cap = cv2.VideoCapture(0, cv2.CAP_DSHOW) if hasattr(cv2, 'CAP_DSHOW') else cv2.VideoCapture(0)
        if not self.cap.isOpened():
            self.cap = None
            return False
        self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, 640)
        self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 480)
        self.running = True
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()
        return True

    def detener(self):
        self.running = False
        if self.thread is not None:
            self.thread.join(timeout=1.5)
            self.thread = None
        if self.cap is not None:
            try:
                self.cap.release()
            except Exception:
                pass
            self.cap = None

    def _loop(self):
        while self.running:
            if self.cap is None:
                break
            ret, frame = self.cap.read()
            if not ret:
                time.sleep(0.05)
                continue
            frame = cv2.flip(frame, 1)
            with self.lock:
                self.last_frame = frame.copy()
            ret2, jpeg = cv2.imencode('.jpg', frame)
            if ret2:
                with self.lock:
                    self.current_jpeg = jpeg.tobytes()
            time.sleep(0.03)

    def get_frame(self):
        with self.lock:
            return self.current_jpeg

    def capturar_encoding(self):
        with self.lock:
            frame = self.last_frame.copy() if self.last_frame is not None else None
        if frame is None:
            return None, "La cámara aún no tiene imagen."
        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        locs = face_recognition.face_locations(rgb, number_of_times_to_upsample=1)
        if not locs:
            return None, "No se detectó ningún rostro."
        encs = face_recognition.face_encodings(rgb, locs, num_jitters=1)
        if not encs:
            return None, "No se pudo procesar el rostro."
        return encs[0], None


def abrir_dialogo_captura(callback_resultado):
    """Abre un diálogo modal con video en vivo y un botón para capturar
    el rostro; al terminar llama a callback_resultado(encoding_o_None)."""
    cam = CapturaCamara()
    ok = cam.iniciar()
    timer_ref = {'t': None}

    with ui.dialog() as dialog, ui.card().classes('items-center q-pa-md'):
        ui.label('Capturar Rostro').classes('text-h6')
        if not ok:
            ui.label('⚠ No se pudo abrir la cámara. Verifique que no esté en uso.') \
                .classes('text-negative q-mt-sm')
            ui.button('Cerrar', on_click=dialog.close).props('flat').classes('q-mt-md')
        else:
            img = ui.interactive_image().style(
                'width:480px;height:360px;background:#000;border-radius:6px'
            )
            estado = ui.label('Coloque su rostro frente a la cámara').classes(
                'text-body2 text-grey-8 q-mt-sm'
            )

            def actualizar_frame():
                frame = cam.get_frame()
                if frame:
                    img.set_source(f'data:image/jpeg;base64,{base64.b64encode(frame).decode()}')

            timer_ref['t'] = ui.timer(0.08, actualizar_frame)

            def capturar():
                encoding, error = cam.capturar_encoding()
                if error:
                    estado.set_text(f'⚠ {error}')
                    return
                estado.set_text('✅ Rostro capturado correctamente.')
                if timer_ref['t']:
                    timer_ref['t'].deactivate()
                cam.detener()
                callback_resultado(encoding)
                dialog.close()

            def cancelar():
                if timer_ref['t']:
                    timer_ref['t'].deactivate()
                cam.detener()
                callback_resultado(None)
                dialog.close()

            with ui.row().classes('q-mt-md q-gutter-sm'):
                ui.button('📸 Capturar Rostro', on_click=capturar).props('color=positive')
                ui.button('Cancelar', on_click=cancelar).props('color=negative flat')

    def limpiar_al_cerrar():
        if timer_ref['t']:
            timer_ref['t'].deactivate()
        cam.detener()

    dialog.on('hide', limpiar_al_cerrar)
    dialog.open()


# ==================== AUTENTICACIÓN ====================
def check_auth(rol_requerido=None):
    """Devuelve True si hay sesión válida (y con el rol correcto).
    Si no, redirige a la página adecuada y devuelve False."""
    usuario = app.storage.user.get('user')
    rol = app.storage.user.get('role')
    if not usuario:
        ui.navigate.to('/login')
        return False
    if rol_requerido and rol != rol_requerido:
        ui.notify('Acceso denegado.', type='negative')
        ui.navigate.to('/')
        return False
    return True


def cerrar_sesion():
    app.storage.user.clear()
    ui.navigate.to('/')


# ==================== PÁGINA PRINCIPAL ====================
@ui.page('/')
def index():
    if not motor.running:
        motor.iniciar()

    procesando = {'activo': False}

    ui.query('body').style('background:#f0f2f5')

    with ui.column().classes('w-full items-center q-pa-md'):
        ui.label('RAE — Registro de Asistencia Estudiantil').classes(
            'text-h4 text-blue-9 text-bold q-mb-xs'
        )
        ui.label(INSTITUCION_NOMBRE).classes('text-subtitle2 text-grey-7 q-mb-md')

        with ui.card().classes('items-center q-pa-md shadow-3'):
            with ui.element('div').style(
                'position:relative;width:640px;height:360px;background:#000;'
                'border-radius:8px;overflow:hidden'
            ):
                video_img = ui.interactive_image().style(
                    'width:640px;height:360px;display:block;object-fit:cover'
                )
                with ui.column().style(
                    'position:absolute;top:0;left:0;width:100%;height:100%;'
                    'background:rgba(0,0,0,0.78);color:white;display:none;'
                    'align-items:center;justify-content:center;text-align:center'
                ) as overlay:
                    overlay_icono = ui.label('🔎').style('font-size:42px')
                    overlay_texto = ui.label('').style(
                        'font-size:17px;font-weight:bold;white-space:pre-line;margin-top:8px'
                    )
                    overlay_progress = ui.linear_progress(value=0).style(
                        'width:380px;margin-top:14px'
                    )

            estado_label = ui.label('Iniciando cámara...').classes('text-h6 text-grey-8 q-mt-sm')
            ui.label('Identificación por cámara activa y en curso').classes(
                'text-caption text-positive'
            )

        async def procesar_deteccion(est_id, nombre, apellido):
            overlay.style('display:flex')
            overlay_icono.set_text('🔎')
            overlay_texto.set_text(f'Verificando a {nombre} {apellido}...')
            overlay_progress.set_visibility(True)
            overlay_progress.value = 0
            pasos = 14
            for i in range(1, pasos + 1):
                overlay_progress.value = i / pasos
                await asyncio.sleep(DURACION_VERIFICACION / pasos)

            tipo, _, _, punt = realizar_registro_db(est_id, nombre, apellido)
            emoji = _emoji_por_tipo(tipo)
            overlay_icono.set_text(emoji)
            overlay_texto.set_text(f'{nombre} {apellido}\n{tipo} registrado\n{punt}')
            overlay_progress.set_visibility(False)
            estado_label.set_text(f'{emoji} {tipo} registrado para {nombre} {apellido}  ({punt})')

            await asyncio.sleep(DURACION_MENSAJE_EXITO)
            overlay.style('display:none')
            motor.desbloquear()
            procesando['activo'] = False

        def actualizar_video():
            frame = motor.get_frame()
            if frame:
                video_img.set_source(f'data:image/jpeg;base64,{base64.b64encode(frame).decode()}')
            if not procesando['activo']:
                estado_label.set_text(motor.estado_texto)
            if motor.pending and not procesando['activo']:
                procesando['activo'] = True
                est_id, nom, ape = motor.pending
                motor.pending = None
                asyncio.create_task(procesar_deteccion(est_id, nom, ape))

        ui.timer(0.05, actualizar_video)

        ui.separator().classes('q-my-md').style('width:640px')

        with ui.row().classes('items-center q-gutter-sm'):
            ui.label('Ingrese ID manual:').classes('text-body1')
            id_input = ui.input().props('outlined dense').classes('w-40')

            def registrar_manual():
                num_id = (id_input.value or '').strip()
                if not num_id:
                    ui.notify('Ingrese un número de identificación.', type='warning')
                    return
                conn = get_connection()
                c = conn.cursor()
                c.execute("SELECT id, nombre, apellido FROM estudiantes WHERE id=?", (num_id,))
                row = c.fetchone()
                conn.close()
                if not row:
                    ui.notify(f'No se encontró el estudiante con ID {num_id}.', type='negative')
                    return
                tipo, nombre, apellido, punt = realizar_registro_db(row[0], row[1], row[2])
                ui.notify(
                    f'{_emoji_por_tipo(tipo)} {nombre} {apellido} (ID {row[0]}) — {tipo} registrado ({punt})',
                    type=_color_notify_por_tipo(tipo), timeout=3000
                )
                id_input.set_value('')

            id_input.on('keydown.enter', registrar_manual)
            ui.button('Identificar', on_click=registrar_manual).props('color=primary')

        ui.separator().classes('q-my-md').style('width:640px')

        # ----- CAMBIO AQUÍ: siempre se cierra sesión antes de ir al login -----
        def ir_login(role):
            # Cerrar sesión existente para forzar la autenticación
            app.storage.user.clear()
            motor.detener()
            ui.navigate.to(f'/login?role={role}')

        with ui.row().classes('q-gutter-xl justify-center q-mb-lg'):
            with ui.column().classes('items-center'):
                ui.button(icon='person', on_click=lambda: ir_login('porteria')).props(
                    'round color=primary size=lg'
                )
                ui.label('Acceso personal').classes('text-caption text-center')
                ui.label('portería').classes('text-caption text-center')
            with ui.column().classes('items-center'):
                ui.button(icon='groups', on_click=lambda: ir_login('admin')).props(
                    'round color=positive size=lg'
                )
                ui.label('Acceso').classes('text-caption text-center')
                ui.label('administrador/director').classes('text-caption text-center')

    ui.context.client.on_disconnect(lambda: motor.detener())


# ==================== LOGIN (siempre muestra el formulario) ====================
@ui.page('/login')
def login_page(role: str = 'porteria'):
    # Ya no redirigimos automáticamente si hay sesión; siempre mostramos el login.
    # Si el usuario ya tiene sesión y llega aquí, podrá volver a autenticarse.

    rol_label = 'Portería' if role == 'porteria' else 'Administrador'

    with ui.column().classes('w-full items-center q-pa-xl'):
        with ui.card().classes('q-pa-lg').style('width:380px'):
            ui.label('Iniciar Sesión').classes('text-h5 text-center q-mb-xs')
            ui.label(f'Acceso: {rol_label}').classes('text-caption text-center text-grey-7 q-mb-md')

            usuario = ui.input('Usuario').props('outlined dense').classes('w-full')
            clave = ui.input('Contraseña', password=True).props('outlined dense').classes('w-full q-mt-sm')

            def hacer_login():
                conn = get_connection()
                c = conn.cursor()
                c.execute(
                    "SELECT rol FROM usuarios WHERE usuario=? AND password=?",
                    (usuario.value or '', clave.value or '')
                )
                row = c.fetchone()
                conn.close()
                if not row:
                    ui.notify('Usuario o contraseña incorrectos.', type='negative')
                    return
                if row[0] != role:
                    ui.notify(f"No tiene permisos de '{role}'.", type='negative')
                    return
                # Guardar sesión y redirigir
                app.storage.user['user'] = usuario.value
                app.storage.user['role'] = row[0]
                ui.navigate.to('/porteria' if role == 'porteria' else '/admin')

            clave.on('keydown.enter', hacer_login)
            ui.button('Entrar', on_click=hacer_login).props('color=primary').classes('full-width q-mt-md')
            ui.button('Volver', on_click=lambda: ui.navigate.to('/')).props('flat').classes('full-width q-mt-sm')


# ==================== PANEL PORTERÍA ====================
@ui.page('/porteria')
def porteria_panel():
    if not check_auth('porteria'):
        return

    with ui.header().classes('bg-primary items-center'):
        ui.label('RAE — Panel de Portería').classes('text-h6')
        ui.space()
        ui.button('🏠 Inicio', on_click=cerrar_sesion).props('flat color=white')
        ui.button('📋 Consultar historial', on_click=lambda: ui.navigate.to('/admin/historial')).props(
            'flat color=white'
        )

    with ui.column().classes('w-full q-pa-md'):
        ui.label('Panel de Monitoreo (Personal de Portería)').classes('text-h5 q-mb-md')

        with ui.row().classes('items-center q-gutter-md'):
            buscar = ui.input(
                'Buscar estudiante', on_change=lambda e: actualizar()
            ).props('outlined dense clearable debounce=300').classes('w-80')
            ui.button('🔄 Actualizar', on_click=lambda: actualizar()).props('flat')
            ui.label('(La lista se filtra y actualiza automáticamente)').classes(
                'text-caption text-grey-7'
            )

        table = ui.table(columns=[
            {'name': 'ID', 'label': 'ID', 'field': 'ID', 'align': 'center', 'sortable': True},
            {'name': 'Estudiante', 'label': 'Estudiante', 'field': 'Estudiante', 'align': 'left', 'sortable': True},
            {'name': 'Fecha', 'label': 'Fecha', 'field': 'Fecha', 'align': 'center', 'sortable': True},
            {'name': 'HoraEntrada', 'label': 'Hora Entrada', 'field': 'HoraEntrada', 'align': 'center'},
            {'name': 'PuntEntrada', 'label': 'Puntualidad Entrada', 'field': 'PuntEntrada', 'align': 'center'},
            {'name': 'HoraSalida', 'label': 'Hora Salida', 'field': 'HoraSalida', 'align': 'center'},
            {'name': 'PuntSalida', 'label': 'Puntualidad Salida', 'field': 'PuntSalida', 'align': 'center'},
            {'name': 'Estado', 'label': 'Estado', 'field': 'Estado', 'align': 'center'},
        ], rows=[], row_key='row_id').classes('w-full q-mt-md')

        def cargar(filtro=''):
            fecha_hoy = datetime.now().strftime("%Y-%m-%d")
            conn = get_connection()
            c = conn.cursor()
            q = """
                SELECT r.id, e.id, e.nombre||' '||e.apellido, r.fecha, r.hora, r.tipo, r.estudiante_id
                FROM registros r
                JOIN estudiantes e ON r.estudiante_id = e.id
                WHERE r.fecha = ?
            """
            params = [fecha_hoy]
            if filtro:
                q += " AND (e.nombre LIKE ? OR e.apellido LIKE ?)"
                params += [f"%{filtro}%", f"%{filtro}%"]
            q += " ORDER BY r.id ASC"
            c.execute(q, params)
            movimientos = c.fetchall()
            conn.close()

            grupos = defaultdict(list)
            for reg_id, est_id, nombre_est, fch, hora, tipo, _ in movimientos:
                grupos[(nombre_est, fch, est_id)].append((tipo, hora, reg_id))

            filas = []
            for (nombre_est, fch, est_id), movs in grupos.items():
                pendiente_ingreso = None
                for tipo, hora, reg_id in movs:
                    if tipo == "Ingreso":
                        if pendiente_ingreso is not None:
                            filas.append((est_id, nombre_est, fch, pendiente_ingreso, "—", "dentro", None))
                        pendiente_ingreso = hora
                    else:
                        if pendiente_ingreso is not None:
                            filas.append((est_id, nombre_est, fch, pendiente_ingreso, hora, "fuera", tipo))
                            pendiente_ingreso = None
                        else:
                            filas.append((est_id, nombre_est, fch, "—", hora, "fuera", tipo))
                if pendiente_ingreso is not None:
                    filas.append((est_id, nombre_est, fch, pendiente_ingreso, "—", "dentro", None))

            filas.sort(key=lambda x: (x[2], x[3]), reverse=True)

            rows = []
            for idx, (est_id, nombre_est, fch, h_ent, h_sal, tag, tipo_sal) in enumerate(filas):
                estado_txt = "✅ Adentro" if tag == "dentro" else "🚪 Salió"
                punt_ent = evaluar_puntualidad_entrada(h_ent) if h_ent != "—" else "—"
                if h_sal != "—":
                    punt_sal = "🟢 Con permiso" if tipo_sal == "Permiso" else evaluar_puntualidad_salida(h_sal)
                else:
                    punt_sal = "—"
                rows.append({
                    'row_id': idx,
                    'ID': est_id,
                    'Estudiante': nombre_est,
                    'Fecha': fch,
                    'HoraEntrada': h_ent,
                    'PuntEntrada': punt_ent,
                    'HoraSalida': h_sal,
                    'PuntSalida': punt_sal,
                    'Estado': estado_txt,
                })
            return rows

        def actualizar():
            table.rows = cargar(buscar.value or '')
            table.update()

        actualizar()
        ui.timer(5.0, actualizar)


# ==================== PANEL ADMINISTRACIÓN ====================
@ui.page('/admin')
def admin_panel():
    if not check_auth('admin'):
        return

    with ui.header().classes('bg-green-9 items-center'):
        ui.label('RAE — Panel de Administración').classes('text-h6')
        ui.space()
        ui.button('🏠 Inicio', on_click=cerrar_sesion).props('flat color=white')

    with ui.column().classes('w-full items-center q-pa-xl'):
        ui.label('Panel de Administración').classes('text-h4 q-mb-lg')
        with ui.row().classes('q-gutter-lg'):
            opciones = [
                ('group', 'Gestionar estudiantes', '/admin/estudiantes'),
                ('history', 'Consultar historial', '/admin/historial'),
                ('summarize', 'Reportes y permisos', '/admin/reportes'),
            ]
            for icon, label, target in opciones:
                with ui.card().classes('items-center q-pa-lg').style('width:220px'):
                    ui.icon(icon, size='48px').classes('text-primary')
                    ui.label(label).classes('text-subtitle1 q-mt-sm text-center')
                    ui.button('Ir', on_click=lambda t=target: ui.navigate.to(t)).props(
                        'color=primary'
                    ).classes('q-mt-sm')


# ==================== GESTIÓN DE ESTUDIANTES ====================
@ui.page('/admin/estudiantes')
def gestion_estudiantes():
    if not check_auth('admin'):
        return

    with ui.header().classes('bg-green-9 items-center'):
        ui.label('RAE — Gestión de Estudiantes').classes('text-h6')
        ui.space()
        ui.button('Volver', on_click=lambda: ui.navigate.to('/admin')).props('flat color=white')

    with ui.column().classes('w-full q-pa-md'):
        ui.label('Gestión de Estudiantes').classes('text-h5 q-mb-sm')

        with ui.row().classes('q-gutter-sm q-mb-sm'):
            ui.button('➕ Añadir Estudiante', on_click=lambda: abrir_formulario()).props('color=primary')
            ui.button('✏️ Editar Estudiante', on_click=lambda: editar_sel()).props('color=grey-8')
            ui.button('🗑 Eliminar Estudiante', on_click=lambda: eliminar_sel()).props('color=negative')
            ui.button('🔢 Reorganizar IDs', on_click=lambda: reorganizar_manual()).props('color=teal')

        buscar = ui.input(
            'Buscar por nombre o ID', on_change=lambda e: actualizar()
        ).props('outlined dense clearable debounce=300').classes('w-96')
        ui.label('(La lista se actualiza automáticamente. Los IDs se reorganizan solos al eliminar un estudiante)').classes(
            'text-caption text-grey-7'
        )

        table = ui.table(columns=[
            {'name': 'id', 'label': 'ID', 'field': 'id', 'align': 'center', 'sortable': True},
            {'name': 'nombre', 'label': 'Nombre', 'field': 'nombre', 'align': 'left', 'sortable': True},
            {'name': 'apellido', 'label': 'Apellido', 'field': 'apellido', 'align': 'left', 'sortable': True},
            {'name': 'grado', 'label': 'Código', 'field': 'grado', 'align': 'center'},
            {'name': 'rostro', 'label': 'Rostro', 'field': 'rostro', 'align': 'center'},
            {'name': 'email', 'label': 'Correo Encargado', 'field': 'email', 'align': 'left'},
        ], rows=[], row_key='id', selection='single').classes('w-full q-mt-sm')

        def cargar(filtro=''):
            conn = get_connection()
            c = conn.cursor()
            q = """
                SELECT e.id, e.nombre, e.apellido, e.grado,
                       CASE WHEN f.id IS NOT NULL THEN '✅ Sí' ELSE '❌ No' END,
                       e.email_encargado
                FROM estudiantes e
                LEFT JOIN estudiantes_faces f ON e.id = f.estudiante_id
            """
            params = []
            if filtro:
                q += " WHERE e.nombre LIKE ? OR e.apellido LIKE ? OR CAST(e.id AS TEXT) LIKE ?"
                params = [f"%{filtro}%"] * 3
            q += " ORDER BY e.id ASC"
            c.execute(q, params)
            rows = c.fetchall()
            conn.close()
            return [
                {'id': r[0], 'nombre': r[1], 'apellido': r[2], 'grado': r[3],
                 'rostro': r[4], 'email': r[5] or ''}
                for r in rows
            ]

        def actualizar():
            table.rows = cargar(buscar.value or '')
            table.selected = []
            table.update()

        def reorganizar_manual():
            cambios = reorganizar_ids_estudiantes()
            actualizar()
            if cambios:
                ui.notify(f'🔢 IDs reorganizados: {cambios} estudiante(s) recibieron un nuevo ID consecutivo.', type='positive')
            else:
                ui.notify('Los IDs ya estaban en orden consecutivo (1, 2, 3, ...).', type='info')

        def editar_sel():
            if not table.selected:
                ui.notify('Seleccione un estudiante de la lista.', type='warning')
                return
            abrir_formulario(table.selected[0]['id'])

        def eliminar_sel():
            if not table.selected:
                ui.notify('Seleccione un estudiante de la lista.', type='warning')
                return
            est_id = table.selected[0]['id']
            with ui.dialog() as confirm, ui.card():
                ui.label('¿Eliminar este estudiante y sus registros?')
                with ui.row().classes('q-mt-sm'):
                    ui.button('Sí', on_click=lambda: hacer_eliminar(est_id, confirm)).props('color=negative')
                    ui.button('No', on_click=confirm.close).props('flat')
            confirm.open()

        def hacer_eliminar(est_id, dialog):
            conn = get_connection()
            c = conn.cursor()
            c.execute("DELETE FROM registros WHERE estudiante_id=?", (est_id,))
            c.execute("DELETE FROM estudiantes_faces WHERE estudiante_id=?", (est_id,))
            c.execute("DELETE FROM estudiantes WHERE id=?", (est_id,))
            conn.commit()
            conn.close()
            # Reorganizar automáticamente para que los IDs de los
            # estudiantes que quedan sigan siendo consecutivos.
            reorganizar_ids_estudiantes()
            dialog.close()
            actualizar()
            ui.notify('Estudiante eliminado. Los IDs se reorganizaron automáticamente.', type='positive')

        def abrir_formulario(est_id=None):
            encoding_holder = {'value': None}
            with ui.dialog() as dialog, ui.card().classes('q-pa-md').style('width:440px'):
                ui.label('Editar Estudiante' if est_id else 'Añadir Estudiante').classes('text-h6 q-mb-sm')

                # Mostrar ID solo si es edición
                if est_id:
                    ui.label(f'ID: {est_id}').classes('text-body2 text-grey-7 q-mb-xs')
                e_nombre = ui.input('Nombre').props('outlined dense').classes('w-full')
                e_apellido = ui.input('Apellido').props('outlined dense').classes('w-full q-mt-xs')
                e_grado = ui.input('Código').props('outlined dense').classes('w-full q-mt-xs')
                e_password = ui.input('Contraseña', password=True).props('outlined dense').classes('w-full q-mt-xs')
                e_email = ui.input('Correo encargado').props('outlined dense').classes('w-full q-mt-xs')

                estado_rostro = ui.label('Sin rostro capturado').classes('text-caption text-grey-7 q-mt-sm')

                if est_id:
                    conn = get_connection()
                    c = conn.cursor()
                    c.execute(
                        "SELECT nombre, apellido, grado, password, email_encargado FROM estudiantes WHERE id=?",
                        (est_id,)
                    )
                    row = c.fetchone()
                    c.execute("SELECT COUNT(*) FROM estudiantes_faces WHERE estudiante_id=?", (est_id,))
                    tiene_rostro = c.fetchone()[0] > 0
                    conn.close()
                    if row:
                        e_nombre.value = row[0]
                        e_apellido.value = row[1]
                        e_grado.value = row[2]
                        e_password.value = row[3]
                        e_email.value = row[4] or ''
                    if tiene_rostro:
                        estado_rostro.set_text('✅ Rostro ya registrado en BD')

                def on_encoding(enc):
                    if enc is not None:
                        encoding_holder['value'] = enc
                        estado_rostro.set_text(f'✅ Rostro listo — {len(enc)} valores, pulse Guardar')
                    else:
                        estado_rostro.set_text('Captura cancelada')

                ui.button(
                    '📸 Capturar Rostro', on_click=lambda: abrir_dialogo_captura(on_encoding)
                ).props('color=grey-8').classes('full-width q-mt-sm')

                def guardar():
                    nombre = (e_nombre.value or '').strip()
                    apellido = (e_apellido.value or '').strip()
                    grado = (e_grado.value or '').strip()
                    password = (e_password.value or '').strip()
                    email = (e_email.value or '').strip()
                    if not (nombre and apellido and grado and password):
                        ui.notify('Complete todos los campos (excepto correo).', type='warning')
                        return
                    conn = get_connection()
                    c = conn.cursor()
                    try:
                        if est_id:
                            c.execute(
                                "UPDATE estudiantes SET nombre=?, apellido=?, grado=?, password=?, "
                                "email_encargado=? WHERE id=?",
                                (nombre, apellido, grado, password, email, est_id)
                            )
                            id_guardado = est_id
                        else:
                            c.execute(
                                "INSERT INTO estudiantes (nombre, apellido, grado, password, email_encargado) "
                                "VALUES (?,?,?,?,?)",
                                (nombre, apellido, grado, password, email)
                            )
                            id_guardado = c.lastrowid
                        if encoding_holder['value'] is not None:
                            blob = pickle.dumps(encoding_holder['value'])
                            c.execute("DELETE FROM estudiantes_faces WHERE estudiante_id=?", (id_guardado,))
                            c.execute(
                                "INSERT INTO estudiantes_faces (estudiante_id, encoding) VALUES (?,?)",
                                (id_guardado, blob)
                            )
                        conn.commit()
                    except Exception as e:
                        conn.rollback()
                        conn.close()
                        ui.notify(f'No se pudo guardar: {e}', type='negative')
                        return
                    conn.close()
                    actualizar()
                    dialog.close()
                    ui.notify('Estudiante guardado correctamente.', type='positive')

                with ui.row().classes('q-mt-md q-gutter-sm justify-end full-width'):
                    ui.button('Cancelar', on_click=dialog.close).props('flat')
                    ui.button('💾 Guardar', on_click=guardar).props('color=primary')
            dialog.open()

        actualizar()


# ==================== CONSULTA DE HISTORIAL (con reporte mejorado) ====================
@ui.page('/admin/historial')
def consulta_historial():
    if not check_auth():
        return
    # Portería también puede entrar aquí (enlace desde su panel); solo exigimos sesión activa.

    with ui.header().classes('bg-green-9 items-center'):
        ui.label('RAE — Consulta de Historial').classes('text-h6')
        ui.space()
        destino_volver = '/porteria' if app.storage.user.get('role') == 'porteria' else '/admin'
        ui.button('Volver', on_click=lambda: ui.navigate.to(destino_volver)).props('flat color=white')

    row_meta = {}

    with ui.column().classes('w-full q-pa-md'):
        ui.label('Consulta de Historial').classes('text-h5 q-mb-sm')
        ui.label(
            f'Horario de registro: entrada hasta {HORA_LIMITE_ENTRADA} · salida a partir de {HORA_LIMITE_SALIDA}. '
            'La columna "Puntualidad Salida" indica si el estudiante salió antes (🟠), '
            'exactamente a tiempo (🟢) o después (🔵) de la hora límite.'
        ).classes('text-caption text-grey-7')

        with ui.row().classes('items-end q-gutter-md'):
            nombre_input = ui.input(
                'Buscar por Nombre', on_change=lambda e: actualizar()
            ).props('outlined dense clearable debounce=300').classes('w-64')
            fecha_input = ui.input(
                'Fecha (AAAA-MM-DD)', on_change=lambda e: actualizar()
            ).props('outlined dense clearable').classes('w-48')

            def abrir_calendario():
                fecha_actual = datetime.now().date()
                if fecha_input.value:
                    try:
                        fecha_actual = datetime.strptime(fecha_input.value, '%Y-%m-%d').date()
                    except Exception:
                        pass
                with ui.dialog() as cal_dialog, ui.card():
                    ui.label('Seleccionar fecha').classes('text-subtitle1')
                    picker = ui.date(value=fecha_actual.isoformat())

                    def usar_hoy():
                        picker.value = datetime.now().date().isoformat()

                    def aceptar():
                        fecha_input.value = picker.value
                        cal_dialog.close()
                        actualizar()

                    with ui.row().classes('q-mt-sm'):
                        ui.button('Hoy', on_click=usar_hoy).props('flat')
                        ui.button('Aceptar', on_click=aceptar).props('color=primary')
                        ui.button('Cancelar', on_click=cal_dialog.close).props('flat')
                cal_dialog.open()

            ui.button('📅', on_click=abrir_calendario).props('flat')

            def limpiar():
                nombre_input.value = ''
                fecha_input.value = ''
                actualizar()

            ui.button('Limpiar', on_click=limpiar).props('flat')

        ui.label('Sin fecha = todo el historial. La lista se actualiza automáticamente.').classes(
            'text-caption text-grey-7'
        )

        with ui.row().classes('q-gutter-sm q-mt-sm'):
            ui.button('🗑 Eliminar seleccionados', on_click=lambda: eliminar_seleccionados()).props(
                'color=negative'
            )
            ui.button('🖨 Imprimir reporte', on_click=lambda: generar_reporte()).props(
                'color=grey-8'
            )

        table = ui.table(columns=[
            {'name': 'ID', 'label': 'ID', 'field': 'ID', 'align': 'center', 'sortable': True},
            {'name': 'Estudiante', 'label': 'Estudiante', 'field': 'Estudiante', 'align': 'left', 'sortable': True},
            {'name': 'Fecha', 'label': 'Fecha', 'field': 'Fecha', 'align': 'center', 'sortable': True},
            {'name': 'HoraEntrada', 'label': 'Hora Entrada', 'field': 'HoraEntrada', 'align': 'center'},
            {'name': 'PuntEntrada', 'label': 'Puntualidad Entrada', 'field': 'PuntEntrada', 'align': 'center'},
            {'name': 'HoraSalida', 'label': 'Hora Salida', 'field': 'HoraSalida', 'align': 'center'},
            {'name': 'PuntSalida', 'label': 'Puntualidad Salida', 'field': 'PuntSalida', 'align': 'center'},
            {'name': 'Estado', 'label': 'Estado', 'field': 'Estado', 'align': 'center'},
        ], rows=[], row_key='row_id', selection='multiple').classes('w-full q-mt-sm')

        def cargar(nombre='', fecha=''):
            conn = get_connection()
            c = conn.cursor()
            q = """
                SELECT r.id, e.id, e.nombre||' '||e.apellido, r.fecha, r.hora, r.tipo, r.estudiante_id
                FROM registros r
                JOIN estudiantes e ON r.estudiante_id = e.id
                WHERE 1=1
            """
            params = []
            if nombre:
                q += " AND (e.nombre||' '||e.apellido LIKE ? OR e.nombre LIKE ? OR e.apellido LIKE ?)"
                params += [f"%{nombre}%", f"%{nombre}%", f"%{nombre}%"]
            if fecha:
                q += " AND r.fecha = ?"
                params.append(fecha)
            q += " ORDER BY r.fecha ASC, r.id ASC"
            c.execute(q, params)
            movimientos = c.fetchall()
            conn.close()

            grupos = defaultdict(list)
            for reg_id, est_id, nombre_est, fch, hora, tipo, _ in movimientos:
                grupos[(nombre_est, fch, est_id)].append((tipo, hora, reg_id))

            filas = []
            for (nombre_est, fch, est_id), movs in grupos.items():
                pendiente_ingreso = None
                pendiente_id = None
                for tipo, hora, reg_id in movs:
                    if tipo == "Ingreso":
                        if pendiente_ingreso is not None:
                            filas.append((est_id, nombre_est, fch, pendiente_ingreso, "—", "dentro",
                                           pendiente_id, None, None))
                        pendiente_ingreso = hora
                        pendiente_id = reg_id
                    else:
                        if pendiente_ingreso is not None:
                            filas.append((est_id, nombre_est, fch, pendiente_ingreso, hora, "fuera",
                                           pendiente_id, reg_id, tipo))
                            pendiente_ingreso = None
                            pendiente_id = None
                        else:
                            filas.append((est_id, nombre_est, fch, "—", hora, "fuera",
                                           None, reg_id, tipo))
                if pendiente_ingreso is not None:
                    filas.append((est_id, nombre_est, fch, pendiente_ingreso, "—", "dentro",
                                   pendiente_id, None, None))

            filas.sort(key=lambda x: (x[2], x[3]), reverse=True)

            rows = []
            row_meta.clear()
            for idx, (est_id, nombre_est, fch, h_ent, h_sal, tag, entrada_id, salida_id, tipo_sal) in enumerate(filas):
                estado_txt = "✅ Adentro" if tag == "dentro" else "🚪 Salió"
                punt_ent = evaluar_puntualidad_entrada(h_ent) if h_ent != "—" else "—"
                if h_sal != "—":
                    punt_sal = "🟢 Con permiso" if tipo_sal == "Permiso" else evaluar_puntualidad_salida(h_sal)
                else:
                    punt_sal = "—"
                rows.append({
                    'row_id': idx,
                    'ID': est_id,
                    'Estudiante': nombre_est,
                    'Fecha': fch,
                    'HoraEntrada': h_ent,
                    'PuntEntrada': punt_ent,
                    'HoraSalida': h_sal,
                    'PuntSalida': punt_sal,
                    'Estado': estado_txt,
                })
                row_meta[idx] = (nombre_est, fch, est_id, entrada_id, salida_id)
            return rows

        def actualizar():
            table.rows = cargar(nombre_input.value or '', fecha_input.value or '')
            table.selected = []
            table.update()

        def eliminar_seleccionados():
            seleccion = table.selected
            if not seleccion:
                ui.notify('Seleccione una o más filas del historial.', type='warning')
                return
            ids_a_eliminar = []
            resumen = []
            for row in seleccion:
                meta = row_meta.get(row['row_id'])
                if not meta:
                    continue
                nombre_est, fch, est_id, entrada_id, salida_id = meta
                if entrada_id:
                    ids_a_eliminar.append(entrada_id)
                if salida_id:
                    ids_a_eliminar.append(salida_id)
                resumen.append(f'{nombre_est} ({fch})')
            if not ids_a_eliminar:
                ui.notify('No se encontraron registros válidos para eliminar.', type='info')
                return
            with ui.dialog() as confirm, ui.card():
                ui.label(
                    f'¿Eliminar {len(seleccion)} fila(s) del historial '
                    f'({len(ids_a_eliminar)} movimiento(s) en la base de datos)?'
                )
                ui.label('\n'.join(resumen)).classes('text-caption text-grey-7').style('white-space:pre-line')
                with ui.row().classes('q-mt-sm'):
                    ui.button(
                        'Sí', on_click=lambda: confirmar_eliminacion(ids_a_eliminar, confirm)
                    ).props('color=negative')
                    ui.button('No', on_click=confirm.close).props('flat')
            confirm.open()

        def confirmar_eliminacion(ids, dialog):
            conn = get_connection()
            c = conn.cursor()
            placeholders = ",".join("?" for _ in ids)
            c.execute(f"DELETE FROM registros WHERE id IN ({placeholders})", ids)
            eliminados = c.rowcount
            conn.commit()
            conn.close()
            dialog.close()
            ui.notify(f'🗑 {eliminados} registro(s) eliminado(s).', type='positive')
            actualizar()

        # ========== FUNCIÓN DE REPORTE (impresión limpia en ventana aparte) ==========
        def generar_reporte():
            """Genera un reporte en formato tabla, bien espaciado, y lo
            manda a imprimir en una ventana nueva y limpia (sin el botón
            'Cerrar' del diálogo ni ningún elemento de la interfaz).

            Cada fila del reporte es un DÍA de un estudiante, con
            columnas separadas para la hora de entrada y la hora de
            salida, y una columna de "Motivo / Puntualidad de salida"
            que indica si salió con permiso (y el motivo), si salió
            antes de tiempo, a tiempo o tarde."""
            seleccion = table.selected
            ids_estudiantes = set()
            if seleccion:
                for row in seleccion:
                    meta = row_meta.get(row['row_id'])
                    if meta:
                        ids_estudiantes.add(meta[2])
            else:
                for meta in row_meta.values():
                    ids_estudiantes.add(meta[2])
            if not ids_estudiantes:
                ui.notify('No hay registros para generar el reporte.', type='info')
                return

            conn = get_connection()
            c = conn.cursor()

            def _badge(texto, color_fondo, color_texto):
                return (
                    f'<span class="badge" style="background:{color_fondo};'
                    f'color:{color_texto};">{texto}</span>'
                )

            def _celda(hora, badge_html):
                # Hora y etiqueta en líneas separadas dentro de un
                # contenedor de ancho completo, para que la etiqueta
                # nunca se salga de la celda sin importar qué tan largo
                # sea el texto (ej. un motivo largo de permiso).
                return f'<div class="cell-stack"><span class="hora">{hora}</span>{badge_html}</div>'

            def _badge_entrada(hora):
                if hora == "—" or not hora:
                    return '<span class="dim">—</span>'
                punt = evaluar_puntualidad_entrada(hora)
                if "Tarde" in punt:
                    return _celda(hora, _badge("Tarde", "#fde2e1", "#b3261e"))
                return _celda(hora, _badge("A tiempo", "#e2f5e9", "#1e7a46"))

            def _badge_salida(hora, tipo_sal, observaciones):
                if hora == "—" or not hora:
                    return '<span class="dim">Aún está en la institución</span>'
                if tipo_sal == "Permiso":
                    motivo = ""
                    if observaciones:
                        motivo = observaciones.replace("Permiso otorgado", "").strip(" -")
                        # La observación guardada en la BD ya trae su propio
                        # prefijo "Motivo: ..." (ver registrar_permiso), así
                        # que se quita aquí para no repetirlo al armar el
                        # texto final ("Salió con permiso — Motivo: X" en
                        # vez de "Con permiso: Motivo: X").
                        if motivo.lower().startswith("motivo:"):
                            motivo = motivo[len("motivo:"):].strip()
                    texto = "Salió con permiso" + (f" — Motivo: {motivo}" if motivo else "")
                    return _celda(hora, _badge(texto, "#fff3d6", "#8a5a00"))
                punt = evaluar_puntualidad_salida(hora)
                if "anticipada" in punt:
                    return _celda(hora, _badge("Salida anticipada", "#ffe6d1", "#a34c00"))
                elif "tardía" in punt:
                    return _celda(hora, _badge("Salida tardía", "#dbe9ff", "#1a4c9c"))
                else:
                    return _celda(hora, _badge("A tiempo", "#e2f5e9", "#1e7a46"))

            bloques_html = []
            hay_datos = False
            for est_id in sorted(ids_estudiantes):
                c.execute("SELECT nombre, apellido, grado FROM estudiantes WHERE id=?", (est_id,))
                datos_est = c.fetchone()
                if not datos_est:
                    continue
                c.execute(
                    "SELECT fecha, hora, tipo, observaciones FROM registros "
                    "WHERE estudiante_id=? ORDER BY fecha ASC, id ASC",
                    (est_id,)
                )
                movimientos = c.fetchall()
                if not movimientos:
                    continue
                hay_datos = True
                nombre_completo = f"{datos_est[0]} {datos_est[1]}"
                codigo = datos_est[2]

                # Agrupar movimientos por fecha, emparejando cada
                # Ingreso con la Salida/Permiso que le sigue (igual que
                # en la tabla de Historial en pantalla).
                por_fecha = defaultdict(list)
                for fecha, hora, tipo, obs in movimientos:
                    por_fecha[fecha].append((tipo, hora, obs))

                filas_dia = []
                for fecha in sorted(por_fecha.keys()):
                    pendiente_hora = None
                    for tipo, hora, obs in por_fecha[fecha]:
                        if tipo == "Ingreso":
                            if pendiente_hora is not None:
                                filas_dia.append((fecha, pendiente_hora, "—", None, None))
                            pendiente_hora = hora
                        else:
                            if pendiente_hora is not None:
                                filas_dia.append((fecha, pendiente_hora, hora, tipo, obs))
                                pendiente_hora = None
                            else:
                                filas_dia.append((fecha, "—", hora, tipo, obs))
                    if pendiente_hora is not None:
                        filas_dia.append((fecha, pendiente_hora, "—", None, None))

                filas_tabla = []
                for fecha, h_ent, h_sal, tipo_sal, obs in filas_dia:
                    filas_tabla.append(
                        "<tr>"
                        f"<td>{fecha}</td>"
                        f"<td>{_badge_entrada(h_ent)}</td>"
                        f"<td>{_badge_salida(h_sal, tipo_sal, obs)}</td>"
                        "</tr>"
                    )

                bloques_html.append(f"""
                <div class="student-block">
                    <div class="student-header">
                        <div class="student-name">{nombre_completo}</div>
                        <div class="student-tags">
                            <span class="tag">ID: {est_id}</span>
                            <span class="tag">Código: {codigo}</span>
                        </div>
                    </div>
                    <table>
                        <thead>
                            <tr><th>Fecha</th><th>Hora de Entrada</th><th>Hora de Salida / Motivo</th></tr>
                        </thead>
                        <tbody>
                            {''.join(filas_tabla)}
                        </tbody>
                    </table>
                    <div class="total">Total de días registrados: {len(filas_dia)}</div>
                </div>
                """)

            conn.close()

            if not hay_datos:
                ui.notify('Ninguno de los estudiantes seleccionados tiene movimientos.', type='info')
                return

            # Documento HTML COMPLETO e independiente (no anidado dentro
            # de la página actual), por eso los estilos se aplican bien
            # y no queda todo pegado. Se abre en una ventana nueva y se
            # manda a imprimir automáticamente; al cerrar la ventana de
            # impresión, la ventana se cierra sola.
            contenido_html = f"""<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<title>Reporte RAE</title>
<style>
    * {{ box-sizing: border-box; }}
    body {{
        font-family: 'Segoe UI', Arial, sans-serif;
        margin: 0;
        padding: 36px 44px;
        color: #222;
        line-height: 1.5;
    }}
    .header {{
        text-align: center;
        font-size: 20px;
        font-weight: 700;
        letter-spacing: 0.3px;
        margin-bottom: 6px;
    }}
    .subheader {{
        text-align: center;
        font-size: 13px;
        color: #555;
        margin-bottom: 28px;
        line-height: 1.7;
    }}
    .subheader b {{ color: #222; }}
    .student-block {{
        margin-top: 30px;
        padding-top: 18px;
        border-top: 2px solid #333;
        page-break-inside: avoid;
    }}
    .student-header {{
        display: flex;
        align-items: baseline;
        justify-content: space-between;
        flex-wrap: wrap;
        margin-bottom: 14px;
        row-gap: 6px;
    }}
    .student-name {{
        font-size: 17px;
        font-weight: 700;
        color: #111;
    }}
    .student-tags {{
        display: flex;
        gap: 8px;
    }}
    .tag {{
        background: #eef1f4;
        border: 1px solid #d5dbe1;
        border-radius: 5px;
        padding: 3px 10px;
        font-size: 12px;
        font-weight: 600;
        color: #333;
        white-space: nowrap;
    }}
    table {{
        width: 100%;
        border-collapse: collapse;
        table-layout: fixed;
    }}
    th, td {{
        border: 1px solid #ccc;
        padding: 10px 14px;
        text-align: center;
        font-size: 13px;
        overflow-wrap: break-word;
        word-break: break-word;
    }}
    .cell-stack {{
        display: flex;
        flex-direction: column;
        align-items: center;
        gap: 3px;
        width: 100%;
    }}
    .cell-stack .hora {{
        font-weight: 600;
    }}
    th {{
        background-color: #eef1f4;
        font-weight: 700;
        text-transform: uppercase;
        font-size: 11.5px;
        letter-spacing: 0.4px;
    }}
    tr:nth-child(even) td {{
        background-color: #fafafa;
    }}
    .badge {{
        display: inline-block;
        padding: 2px 9px;
        border-radius: 10px;
        font-size: 11.5px;
        font-weight: 700;
        margin-top: 3px;
        white-space: normal;
        word-break: break-word;
        max-width: 100%;
        line-height: 1.35;
    }}
    .dim {{
        color: #888;
        font-style: italic;
        font-size: 12.5px;
    }}
    .total {{
        margin-top: 10px;
        font-size: 12.5px;
        color: #555;
        font-style: italic;
        text-align: right;
    }}
    @media print {{
        body {{ padding: 12mm 14mm; }}
        .student-block {{ break-inside: avoid; }}
    }}
</style>
</head>
<body>
    <div class="header">REGISTRO DE ASISTENCIA ESTUDIANTIL (RAE)</div>
    <div class="subheader">
        <b>{INSTITUCION_NOMBRE}</b><br>
        Generado: {datetime.now().strftime('%Y-%m-%d %I:%M %p')}<br>
        Alcance: {'Estudiantes seleccionados' if seleccion else 'Todos los estudiantes de la tabla'}<br>
        Horario: entrada hasta {HORA_LIMITE_ENTRADA} · salida a partir de {HORA_LIMITE_SALIDA}
    </div>
    {''.join(bloques_html)}
    <script>
        window.onload = function() {{
            window.print();
        }};
        window.onafterprint = function() {{
            window.close();
        }};
    </script>
</body>
</html>"""

            # Se codifica en base64 (UTF-8) y se abre en una pestaña
            # nueva para que la impresión sea 100% independiente de la
            # interfaz de NiceGUI. IMPORTANTE: se decodifica con
            # TextDecoder('utf-8') en JS antes de escribirlo -- si se
            # usa document.write(atob(...)) directamente, los bytes
            # UTF-8 de tildes/eñes se interpretan mal y salen símbolos
            # corruptos (ej. "TÃ©CNICO" en vez de "TÉCNICO").
            b64 = base64.b64encode(contenido_html.encode('utf-8')).decode('ascii')
            ui.run_javascript(f"""
                const b64 = '{b64}';
                const bytes = Uint8Array.from(atob(b64), ch => ch.charCodeAt(0));
                const html = new TextDecoder('utf-8').decode(bytes);
                const w = window.open('', '_blank');
                w.document.open();
                w.document.write(html);
                w.document.close();
            """)
            ui.notify('Generando reporte para imprimir…', type='positive', timeout=1500)

        actualizar()


# ==================== REPORTES Y PERMISOS ====================
@ui.page('/admin/reportes')
def panel_reportes():
    if not check_auth('admin'):
        return

    with ui.header().classes('bg-green-9 items-center'):
        ui.label('RAE — Reportes y Permisos').classes('text-h6')
        ui.space()
        ui.button('Volver', on_click=lambda: ui.navigate.to('/admin')).props('flat color=white')

    with ui.column().classes('w-full q-pa-md'):
        ui.label('Gestión de Permisos y Reportes').classes('text-h5 q-mb-sm')

        with ui.card().classes('q-pa-md q-mb-md w-full'):
            ui.label('Registrar un permiso').classes('text-h6 q-mb-sm')

            conn = get_connection()
            c = conn.cursor()
            c.execute("SELECT id, nombre||' '||apellido FROM estudiantes ORDER BY id")
            estudiantes = c.fetchall()
            conn.close()
            opciones_est = {est_id: f'{est_id} - {nombre}' for est_id, nombre in estudiantes}

            with ui.row().classes('items-end q-gutter-md'):
                combo = ui.select(
                    options=opciones_est, label='Estudiante',
                    value=(estudiantes[0][0] if estudiantes else None)
                ).props('outlined dense').classes('w-64')
                motivo_input = ui.input('Motivo (opcional)').props('outlined dense').classes('w-64')

                def registrar_permiso():
                    est_id = combo.value
                    if not est_id:
                        ui.notify('Seleccione un estudiante.', type='warning')
                        return
                    motivo = (motivo_input.value or '').strip()
                    conn2 = get_connection()
                    c2 = conn2.cursor()
                    c2.execute("SELECT nombre, apellido, email_encargado FROM estudiantes WHERE id=?", (est_id,))
                    row = c2.fetchone()
                    if not row:
                        ui.notify('Estudiante no encontrado.', type='negative')
                        conn2.close()
                        return
                    nombre, apellido, email = row
                    ahora = datetime.now()
                    fecha = ahora.strftime("%Y-%m-%d")
                    hora = ahora.strftime("%I:%M %p")
                    observacion = "Permiso otorgado" + (f" - Motivo: {motivo}" if motivo else "")
                    c2.execute("""
                        INSERT INTO registros (estudiante_id, tipo, fecha, hora, observaciones, registrado_por)
                        VALUES (?, 'Permiso', ?, ?, ?, 'Administrador')
                    """, (est_id, fecha, hora, observacion))
                    conn2.commit()
                    conn2.close()
                    ui.notify(f'📝 Permiso registrado para {nombre} {apellido} (ID {est_id})', type='warning')
                    motivo_input.value = ''
                    actualizar_permisos()
                    if email:
                        if enviar_correo_permiso(f'{nombre} {apellido}', fecha, hora, email, motivo):
                            ui.notify(f'Correo enviado a {email}', type='positive')
                        else:
                            ui.notify(f'No se pudo enviar a {email}', type='negative')

                ui.button('📝 Registrar Permiso', on_click=registrar_permiso).props('color=orange')

        with ui.card().classes('q-pa-md w-full'):
            ui.label('Permisos registrados — hoy').classes('text-h6 q-mb-sm')
            tabla_permisos = ui.table(columns=[
                {'name': 'idx', 'label': 'N°', 'field': 'idx', 'align': 'center'},
                {'name': 'ID', 'label': 'ID Estudiante', 'field': 'ID', 'align': 'center'},
                {'name': 'Estudiante', 'label': 'Estudiante', 'field': 'Estudiante', 'align': 'left'},
                {'name': 'Fecha', 'label': 'Fecha', 'field': 'Fecha', 'align': 'center'},
                {'name': 'Hora', 'label': 'Hora', 'field': 'Hora', 'align': 'center'},
                {'name': 'Motivo', 'label': 'Motivo', 'field': 'Motivo', 'align': 'left'},
                {'name': 'Correo', 'label': 'Correo Encargado', 'field': 'Correo', 'align': 'left'},
            ], rows=[], row_key='idx').classes('w-full')

        def cargar_permisos(fecha=None):
            if not fecha:
                fecha = datetime.now().strftime("%Y-%m-%d")
            conn3 = get_connection()
            c3 = conn3.cursor()
            c3.execute("""
                SELECT r.id, e.id, e.nombre||' '||e.apellido, r.fecha, r.hora, r.observaciones, e.email_encargado
                FROM registros r
                JOIN estudiantes e ON r.estudiante_id = e.id
                WHERE r.tipo = 'Permiso' AND r.fecha = ?
                ORDER BY r.id ASC
            """, (fecha,))
            rows = c3.fetchall()
            conn3.close()
            data = []
            for idx, (reg_id, est_id, estudiante, fch, hora, obs, email) in enumerate(rows, start=1):
                motivo = (obs or '').replace("Permiso otorgado", "").strip(" -")
                data.append({
                    'idx': idx,
                    'ID': est_id,
                    'Estudiante': estudiante,
                    'Fecha': fch,
                    'Hora': hora,
                    'Motivo': motivo or '—',
                    'Correo': email or '—',
                })
            return data

        def actualizar_permisos():
            tabla_permisos.rows = cargar_permisos()
            tabla_permisos.update()

        actualizar_permisos()


# ==================== ARRANQUE ====================
if __name__ in {'__main__', '__mp_main__'}:
    init_db()
    ui.run(
        title='RAE — Asistencia Estudiantil',
        port=8080,
        reload=False,
        storage_secret=STORAGE_SECRET,
    )