import sqlite3

DB_FILE = "rae.db"

def get_connection():
    return sqlite3.connect(DB_FILE)
conn = get_connection()   # 1. Abrir conexión
c = conn.cursor()         # 2. Crear cursor (para ejecutar SQL)
c.execute("...")          # 3. Ejecutar consulta
conn.commit()             # 4. Guardar cambios (solo en INSERT/UPDATE/DELETE)
conn.close()              # 5. Cerrar conexión
c.execute("SELECT id, nombre, apellido FROM estudiantes WHERE id=?", (num_id,)) # type: ignore
row = c.fetchone()   # Un solo resultado
# o
rows = c.fetchall()  # Todos los resultados
c.execute("""
    INSERT INTO registros (estudiante_id, tipo, fecha, hora, observaciones)
    VALUES (?,?,?,?,?)
""", (est_id, tipo, fecha, hora, "Registrado automáticamente")) # type: ignore
conn.commit()  # ← Obligatorio para guardar
c.execute("""
    UPDATE estudiantes SET nombre=?, apellido=?, grado=? WHERE id=?
""", (nombre, apellido, grado, self.est_id)) # type: ignore
conn.commit()
# ✅ Correcto (tu código lo hace así)
c.execute("SELECT * FROM estudiantes WHERE id=?", (num_id,)) # type: ignore

# ❌ Peligroso (nunca hagas esto)
c.execute(f"SELECT * FROM estudiantes WHERE id={num_id}") # type: ignore